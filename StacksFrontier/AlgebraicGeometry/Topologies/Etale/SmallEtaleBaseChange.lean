module

public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismCriteria
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change between small étale sites, and the resulting factorizations

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of its underlying category.
Pulling an étale `S`-scheme back along `f` is an étale `T`-scheme, so base change is a functor
from the small étale category of `S` to that of `T`. That functor is continuous, and in fact a
morphism of sites; it therefore represents a geometric morphism `f_small : T_ét ⟶ S_ét`, the
site functor running opposite to the morphism of topoi.

This file constructs that functor and then records how the morphisms of topoi attached to `f`
relate to one another:

* restriction from the big to the small site commutes with base change, as a square of site
  functors and hence of direct images;
* the morphism from the small étale topos of `T` to the big étale topos over `S` factors
  through the big étale topos over `T`;
* `f_small` factors through the inclusion of `T_ét`, the big-site morphism along `f`, and the
  projection to `S_ét` — equivalently through the direct morphism `i_f` and that projection.

## Main definitions

* `AlgebraicGeometry.smallEtaleBaseChange` — base change along `f` on small étale categories.

## Main results

* `AlgebraicGeometry.smallEtaleBaseChange_coverPreserving` — base change carries covering sieves
  to covering sieves.
* `AlgebraicGeometry.smallEtaleBaseChange_isContinuous` and
  `AlgebraicGeometry.smallEtaleBaseChange_isMorphismOfSites` — base change is continuous, and
  is a morphism of sites.
* `AlgebraicGeometry.smallEtaleBaseChange_comp_inclusion` and
  `AlgebraicGeometry.bigSmallEtalePushforwardCommIso` — the commuting square, on site functors
  and on direct images.
* `AlgebraicGeometry.smallEtaleToBigEtaleMorphism_comp_inverseImageIso` and
  `AlgebraicGeometry.smallEtaleToBigEtaleMorphism_comp_pushforwardIso` — the factorization
  through the big étale topos over `T`.
* `AlgebraicGeometry.smallEtalePushforwardIsoBigFactorization` and
  `AlgebraicGeometry.smallEtalePushforwardIsoDirectFactorization` — the two factorizations of
  the small-site direct image.
* `AlgebraicGeometry.smallEtaleBaseChange_isCovering` — base change carries a covering family
  of the small étale category of `S` to one of `T`.
* `AlgebraicGeometry.isSheafFor_baseChange_iff` — a presheaf on the small étale category of
  `T` satisfies the sheaf condition for the base change of a covering family exactly when its
  direct image satisfies it for the original family. Together with
  `CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf` this is why the direct image of a sheaf
  is a sheaf.
* `AlgebraicGeometry.smallEtaleSheafPullback_preservesFiniteLimits` — inverse image between
  the small étale topoi preserves finite limits. It preserves all colimits as a left adjoint,
  so it is exact.

## Implementation notes

Base change is the restriction of `CategoryTheory.Over.pullback` to étale objects, obtained by
lifting it along the full subcategory inclusion; `smallEtaleBaseChange_comp_inclusion` records
that the lift composed with the inclusion is the slice pullback on the nose, and every
preservation property of base change is transported across that equality.

The source states equalities of morphisms of sites and of topoi. Chosen fibre products and
chosen adjoints make those equalities canonical natural isomorphisms here: a direct-image
comparison is induced by the comparison of the underlying site functors, and an inverse-image
comparison is its mate under the geometric adjunctions. Stating them as isomorphisms of
functors, rather than as equalities of section sets, retains naturality in the sheaf and in the
object.

Being a morphism of sites requires an exact left adjoint, which the general theory supplies for
a representably flat functor between *small* sites. The small étale categories have their
objects and their morphisms in different universes, so the statement is transported along
`CategoryTheory.equivSmallModel` in each variable and then carried back; the four
`rootMorphismOfSites_of_*` helpers are that transport, for a small site, an equivalence, the
inverse of an equivalence, and an isomorphic functor.

## References

* [Stacks Project, Lemma 34.4.6 (Tag 021I)](https://stacks.math.columbia.edu/tag/021I)
* [Stacks Project, Tag 03PX](https://stacks.math.columbia.edu/tag/03PX)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u})

/-- A family of pullbacks of a chosen covering family of a big étale site, taken along a
morphism of the site, is again a chosen covering family. -/
private lemma isCovering_of_isPullback {X Y : B.Scheme}
    (E : PreZeroHypercover.{u + 1} X) (hE : B.IsCovering ⟨X, E⟩) (g : Y ⟶ X)
    (P : E.I₀ → B.Scheme) (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ E.X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (E.f i)) :
    B.IsCovering ⟨Y, ⟨E.I₀, P, p₁⟩⟩ := by
  refine ⟨?_, hE.2⟩
  show (PreZeroHypercover.mk E.I₀ P p₁ |>.map B.inclusion).presieve₀ ∈
    Scheme.etalePrecoverage (B.inclusion.obj Y)
  apply Precoverage.mem_coverings_of_isPullback
    (f := fun i => B.inclusion.map (E.f i))
    (hR := hE.1) (g := B.inclusion.map g)
    (p₁ := fun i => B.inclusion.map (p₁ i))
    (p₂ := fun i => B.inclusion.map (p₂ i))
  exact fun i => (h i).map B.inclusion

/-- The slice base change of a chosen covering family of a big étale slice is again a chosen
covering family. -/
private lemma isCovering_overPullback {S T : B.Scheme} (f : T ⟶ S)
    {X : Over S} (E : PreZeroHypercover.{u + 1} X)
    (hE : B.IsCovering ⟨X.left, E.map (Over.forget S)⟩) :
    B.IsCovering ⟨((Over.pullback f).obj X).left,
      (E.map (Over.pullback f)).map (Over.forget T)⟩ := by
  apply isCovering_of_isPullback B (E.map (Over.forget S)) hE
    (pullback.fst X.hom f)
    (fun i => ((Over.pullback f).obj (E.X i)).left)
    (fun i => ((Over.pullback f).map (E.f i)).left)
    (fun i => pullback.fst (E.X i).hom f)
  intro i
  show IsPullback
    (pullback.lift (pullback.fst (E.X i).hom f ≫ (E.f i).left)
      (pullback.snd (E.X i).hom f) _)
    (pullback.fst (E.X i).hom f) (pullback.fst X.hom f) (E.f i).left
  exact baseChange_square (E.f i).left X.hom (E.X i).hom f (Over.w (E.f i))

/-- Base change along `f : T ⟶ S` sends an étale scheme over `S` to its fibre product
with `T` over `S`, regarded as an étale scheme over `T`. -/
public noncomputable def smallEtaleBaseChange {S T : B.Scheme} (f : T ⟶ S) :
    SmallEtale B S.obj S.property ⥤ SmallEtale B T.obj T.property := by
  refine (BigEtaleOver.IsEtaleOver B T.obj T.property).lift
    (SmallEtale.inclusion B S.obj S.property ⋙ Over.pullback f) ?_
  intro X
  change Etale (B.inclusion.map (pullback.snd X.obj.hom f))
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback X.obj.hom f).map B.inclusion) X.property

/-- The underlying object over `T` is the usual pullback of the object over `S`. -/
@[simp]
public theorem smallEtaleBaseChange_obj_obj {S T : B.Scheme} (f : T ⟶ S)
    (X : SmallEtale B S.obj S.property) :
    ((smallEtaleBaseChange B f).obj X).obj = (Over.pullback f).obj X.obj := rfl

/-- Forgetting the étale condition identifies small étale base change with pullback in
slice categories, on both objects and morphisms. -/
public theorem smallEtaleBaseChange_comp_inclusion {S T : B.Scheme} (f : T ⟶ S) :
    smallEtaleBaseChange B f ⋙ SmallEtale.inclusion B T.obj T.property =
      SmallEtale.inclusion B S.obj S.property ⋙ Over.pullback f := rfl

add_to_stacks 021I "commutative_diagram"
  AlgebraicGeometry.smallEtaleBaseChange_comp_inclusion

/-- Small étale base change preserves a limit that slice pullback preserves on small étale
objects, since the inclusion into the slice reflects limits. -/
private lemma preservesLimit_smallEtaleBaseChange {S T : B.Scheme} (f : T ⟶ S)
    {J : Type} [Category J] (K : J ⥤ SmallEtale B S.obj S.property)
    [PreservesLimit K (SmallEtale.inclusion B S.obj S.property ⋙ Over.pullback f)] :
    PreservesLimit K (smallEtaleBaseChange B f) := by
  have := preservesLimit_of_natIso K
    (eqToIso (smallEtaleBaseChange_comp_inclusion B f).symm)
  exact preservesLimit_of_reflects_of_preserves
    (smallEtaleBaseChange B f) (SmallEtale.inclusion B T.obj T.property)

/-- Small étale base change preserves fibre products.

This is deliberately private: it exists only to feed
`AlgebraicGeometry.preservesFiniteLimits_smallEtaleBaseChange` below, which is public and from
which every finite shape follows by
`CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits`. Downstream modules should
use that instance rather than restating this one. -/
@[ega "I 3.3.10" "special case"]
private instance preservesPullbacks_baseChange {S T : B.Scheme} (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (smallEtaleBaseChange B f) :=
  ⟨preservesLimit_smallEtaleBaseChange B f _⟩

/-- Small étale base change preserves the final object. -/
private instance preservesTerminal_baseChange {S T : B.Scheme} (f : T ⟶ S) :
    PreservesLimit (Functor.empty.{0} (SmallEtale B S.obj S.property))
      (smallEtaleBaseChange B f) :=
  preservesLimit_smallEtaleBaseChange B f _

/-- Small étale base change preserves finite limits: it preserves the final object and fibre
products, and the small étale category has all finite limits. -/
public instance preservesFiniteLimits_smallEtaleBaseChange {S T : B.Scheme} (f : T ⟶ S) :
    PreservesFiniteLimits (smallEtaleBaseChange B f) := by
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (smallEtaleBaseChange B f) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal (smallEtaleBaseChange B f)
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- Small étale base change is representably flat. -/
public instance representablyFlat_smallEtaleBaseChange {S T : B.Scheme} (f : T ⟶ S) :
    RepresentablyFlat (smallEtaleBaseChange B f) :=
  flat_of_preservesFiniteLimits _

/-- Pulling an étale covering family of `S` back along `f : T ⟶ S` yields an étale covering
family of `T`. -/
@[stacks 03PX "pullback of coverings"]
public theorem smallEtaleBaseChange_isCovering {S T : B.Scheme} (f : T ⟶ S)
    (E : Covering (SmallEtale B S.obj S.property))
    (hE : SmallEtale.IsCovering B S.obj S.property E) :
    SmallEtale.IsCovering B T.obj T.property
      ⟨(smallEtaleBaseChange B f).obj E.1, E.2.map (smallEtaleBaseChange B f)⟩ := by
  show B.IsCovering _
  exact isCovering_overPullback B (T := B.obj T.obj T.property) f
    (E.2.map (SmallEtale.inclusion B S.obj S.property)) hE

/-- The sheaf condition for a presheaf on the small étale category of `T`, tested against the
base change of a covering family of `S`, agrees with the sheaf condition for its direct image
tested against the original family. -/
@[stacks 03PX "sheaf condition"]
public theorem isSheafFor_baseChange_iff {S T : B.Scheme} (f : T ⟶ S)
    (P : (SmallEtale B T.obj T.property)ᵒᵖ ⥤ Type v)
    (E : Covering (SmallEtale B S.obj S.property)) :
    Presieve.IsSheafFor ((smallEtaleBaseChange B f).op ⋙ P) E.2.presieve₀ ↔
      Presieve.IsSheafFor P (E.2.map (smallEtaleBaseChange B f)).presieve₀ := by
  rw [PreZeroHypercover.presieve₀_map]
  exact Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks
    (smallEtaleBaseChange B f) P E.2.presieve₀

add_to_stacks 03PX "direct image of a sheaf"
  CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf

/-- Small étale base change carries covering sieves to covering sieves. -/
public theorem smallEtaleBaseChange_coverPreserving {S T : B.Scheme} (f : T ⟶ S) :
    CoverPreserving (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property) (smallEtaleBaseChange B f) := by
  apply coverPreserving_of_generators
    (smallEtaleBaseChange B f) (SmallEtale.precoverage B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := (SmallEtale.mem_precoverage_iff B S.obj S.property).1 hR
  rw [← PreZeroHypercover.sieve₀_map]
  exact Precoverage.generate_mem_toGrothendieck
    ((SmallEtale.mem_precoverage_iff B T.obj T.property).2
      ⟨E.map (smallEtaleBaseChange B f), rfl, smallEtaleBaseChange_isCovering B f ⟨X, E⟩ hE⟩)

/-- **Stacks 021I, base-change continuity.** Base change along a morphism in a big étale
site is a continuous functor between the corresponding small étale sites. -/
@[stacks 021I "base_change_continuous"]
public instance smallEtaleBaseChange_isContinuous {S T : B.Scheme} (f : T ⟶ S) :
    Functor.IsContinuous (smallEtaleBaseChange B f)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property) := by
  have : HasFiniteLimits (SmallEtale B S.obj S.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  exact Functor.isContinuous_iff_coverPreserving.2 (smallEtaleBaseChange_coverPreserving B f)

section MorphismOfSites

universe w v₁ v₂ u₁ u₂

/-- **Stacks 021I, small étale morphism.** Base change along `f : T ⟶ S` defines a
morphism of sites from the small étale site of `T` to that of `S`. -/
@[stacks 021I "small_etale_morphism"]
public instance smallEtaleBaseChange_isMorphismOfSites {S T : B.Scheme} (f : T ⟶ S) :
    IsMorphismOfSites.{u + 1} (smallEtaleBaseChange B f)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property) := by
  let C := SmallEtale B S.obj S.property
  let D := SmallEtale B T.obj T.property
  let J := SmallEtale.topology B S.obj S.property
  let K := SmallEtale.topology B T.obj T.property
  let F := smallEtaleBaseChange B f
  have : RepresentablyFlat F := representablyFlat_smallEtaleBaseChange B f
  let eC := equivSmallModel.{u + 1} C
  let eD := equivSmallModel.{u + 1} D
  let J' := eC.inverse.inducedTopology J
  let K' := eD.inverse.inducedTopology K
  let F' := eC.inverse ⋙ F ⋙ eD.functor
  have : F.IsContinuous J K := smallEtaleBaseChange_isContinuous B f
  have : (eC.inverse ⋙ F).IsContinuous J' K :=
    Functor.isContinuous_comp eC.inverse F J' J K
  have : F'.IsContinuous J' K' :=
    Functor.isContinuous_comp (eC.inverse ⋙ F) eD.functor J' K K'
  have hF' : F'.IsMorphismOfSites J' K' :=
    Functor.isMorphismOfSites_of_representablyFlat F' J' K'
  have hF'root : _root_.IsMorphismOfSites.{u + 1} F' J' K' :=
    rootMorphismOfSites_of_small F' J' K' hF'
  have hC : _root_.IsMorphismOfSites.{u + 1} eC.functor J J' :=
    rootMorphismOfSites_of_equivalence eC J J'
  have hD : _root_.IsMorphismOfSites.{u + 1} eD.inverse K' K :=
    rootMorphismOfSites_of_equivalence_inverse eD K K'
  have hMid : _root_.IsMorphismOfSites.{u + 1} (F' ⋙ eD.inverse) J' K :=
    isMorphismOfSites_comp K K' J' F' eD.inverse
  have hAll : _root_.IsMorphismOfSites.{u + 1} (eC.functor ⋙ (F' ⋙ eD.inverse)) J K :=
    isMorphismOfSites_comp K J' J eC.functor (F' ⋙ eD.inverse)
  let i : eC.functor ⋙ (F' ⋙ eD.inverse) ≅ F := by
    dsimp [F']
    exact NatIso.ofComponents (fun X =>
      (eD.unitIso.app (F.obj (eC.inverse.obj (eC.functor.obj X)))).symm ≪≫
        F.mapIso (eC.unitIso.app X).symm) (fun _ => by simp)
  exact rootMorphismOfSites_of_iso i.symm J K hAll

end MorphismOfSites

/-- Inverse image along `f : T ⟶ S` between the small étale topoi preserves finite limits:
being a morphism of sites, base change has an exact left adjoint on sheaves, and that left
adjoint is the sheaf pullback. -/
@[stacks 03Q1 "exact_sets"]
public instance smallEtaleSheafPullback_preservesFiniteLimits {S T : B.Scheme} (f : T ⟶ S) :
    PreservesFiniteLimits
      ((smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)) := by
  obtain ⟨L, ⟨adj⟩, hL⟩ := (smallEtaleBaseChange_isMorphismOfSites B f).hasExactLeftAdjoint
  exact preservesFiniteLimits_of_natIso (adj.leftAdjointUniq
    ((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)))

add_to_stacks 03Q1 "exact_sets" CategoryTheory.Adjunction.leftAdjoint_preservesColimits

variable (T S : B.Scheme) (f : T ⟶ S)

include f

/-- **Stacks 021I, commutative diagram.** The square formed by small étale base change, big
étale base change, and the two projections from big to small étale topoi commutes on direct
images. -/
@[stacks 021I "commutative_diagram"]
public noncomputable def bigSmallEtalePushforwardCommIso :
    (bigEtaleToSmallEtaleMorphism B T.obj T.property).pushforward ⋙
        (smallEtaleBaseChange B f).sheafPushforwardContinuous
          (Type (u + 1)) (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property) ≅
      (bigEtaleMorphism B T S f).pushforward ⋙
        (bigEtaleToSmallEtaleMorphism B S.obj S.property).pushforward := by
  letI : (smallEtaleBaseChange B f ⋙
      SmallEtale.inclusion B T.obj T.property).IsContinuous
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property) :=
    Functor.isContinuous_comp
      (smallEtaleBaseChange B f) (SmallEtale.inclusion B T.obj T.property)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)
  letI : (SmallEtale.inclusion B S.obj S.property ⋙
      Over.pullback f).IsContinuous
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property) :=
    Functor.isContinuous_comp
      (SmallEtale.inclusion B S.obj S.property) (Over.pullback f)
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property)
  exact (smallEtaleBaseChange B f).sheafPushforwardContinuousComp
      (SmallEtale.inclusion B T.obj T.property) (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property) ≪≫
    Functor.sheafPushforwardContinuousIso
      (eqToIso (smallEtaleBaseChange_comp_inclusion B f))
      (Type (u + 1)) (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property) ≪≫
    ((SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuousComp
      (Over.pullback f) (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property)).symm ≪≫
    Functor.isoWhiskerRight
      (bigEtaleMorphismPushforwardIso B T S f).symm
      (bigEtaleToSmallEtaleMorphism B S.obj S.property).pushforward

/-- **Stacks 021I, big-site factorization.** The inverse-image functor of `i_f` is naturally
isomorphic to the inverse image of `f_big ∘ i_T`. -/
@[stacks 021I "big_site_factorization"]
public noncomputable def smallEtaleToBigEtaleMorphism_comp_inverseImageIso :
    (smallEtaleToBigEtaleMorphism B T S f).inverseImage ≅
      (bigEtaleMorphism B T S f).inverseImage ⋙
        (smallEtaleToBigEtaleMorphism B T T (𝟙 T)).inverseImage := by
  let J := SmallEtale.topology B T.obj T.property
  let K := BigEtaleOver.topology B T.obj T.property
  let L := BigEtaleOver.topology B S.obj S.property
  let F := smallEtaleToBigEtaleFunctor B T T (𝟙 T)
  let G := Over.map f
  let H := smallEtaleToBigEtaleFunctor B T S f
  letI : H.IsContinuous J L := smallEtaleToBigEtaleFunctor_isContinuous B T S f
  have hsite : F ⋙ G = H := by
    dsimp [F, G, H, smallEtaleToBigEtaleFunctor]
    rw [Over.mapId_eq]
    rfl
  let hF := Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    F (Type (u + 1)) J K
  let hH := Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    H (Type (u + 1)) J L
  let hG := bigEtaleMorphismInverseImageIso B T S f
  exact hH ≪≫
    (Functor.sheafPushforwardContinuousComp' (F := F) (G := G) (FG := H)
      (eqToIso hsite) (Type (u + 1)) J K L).symm ≪≫
    (Functor.isoWhiskerRight hG.symm _ ≪≫ Functor.isoWhiskerLeft _ hF.symm)

/-- **Stacks 021I, big-site factorization.** The direct-image comparison for
`i_f = f_big ∘ i_T`, naturally in the small étale sheaf. -/
@[stacks 021I "big_site_factorization"]
public noncomputable def smallEtaleToBigEtaleMorphism_comp_pushforwardIso :
    (smallEtaleToBigEtaleMorphism B T S f).pushforward ≅
      (smallEtaleToBigEtaleMorphism B T T (𝟙 T)).pushforward ⋙
        (bigEtaleMorphism B T S f).pushforward :=
  (conjugateIsoEquiv
    (smallEtaleToBigEtaleMorphism B T S f).adj
    ((bigEtaleMorphism B T S f).adj.comp
      (smallEtaleToBigEtaleMorphism B T T (𝟙 T)).adj))
    (smallEtaleToBigEtaleMorphism_comp_inverseImageIso B T S f).symm

/-- **Stacks 021I, small-site factorization.** The small étale direct image is canonically the
composite of inclusion into the big étale topos over `T`, big-site direct image along `f`, and
projection to the small étale topos of `S`. -/
@[stacks 021I "small_site_factorization"]
public noncomputable def smallEtalePushforwardIsoBigFactorization :
    (smallEtaleBaseChange B f).sheafPushforwardContinuous
        (Type (u + 1)) (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property) ≅
      (smallEtaleToBigEtaleMorphism B T T (𝟙 T)).pushforward ⋙
        (bigEtaleMorphism B T S f).pushforward ⋙
          (bigEtaleToSmallEtaleMorphism B S.obj S.property).pushforward := by
  let iT := (smallEtaleToBigEtaleMorphism B T T (𝟙 T)).pushforward
  let piT := (bigEtaleToSmallEtaleMorphism B T.obj T.property).pushforward
  let fSmall := (smallEtaleBaseChange B f).sheafPushforwardContinuous
    (Type (u + 1)) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)
  let fBig := (bigEtaleMorphism B T S f).pushforward
  let piS := (bigEtaleToSmallEtaleMorphism B S.obj S.property).pushforward
  exact (Functor.leftUnitor fSmall).symm ≪≫
    (Functor.isoWhiskerRight
      (projectionCompInclusionPushforwardIso B T.obj T.property) fSmall).symm ≪≫
    Functor.associator iT piT fSmall ≪≫
    Functor.isoWhiskerLeft iT (bigSmallEtalePushforwardCommIso B T S f) ≪≫
    (Functor.associator iT fBig piS).symm

/-- **Stacks 021I, small-site factorization.** The small étale direct image is canonically the
composite of the direct morphism `i_f` to the big étale topos over `S` and its projection. -/
@[stacks 021I "small_site_factorization"]
public noncomputable def smallEtalePushforwardIsoDirectFactorization :
    (smallEtaleBaseChange B f).sheafPushforwardContinuous
        (Type (u + 1)) (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property) ≅
      (smallEtaleToBigEtaleMorphism B T S f).pushforward ⋙
        (bigEtaleToSmallEtaleMorphism B S.obj S.property).pushforward :=
  smallEtalePushforwardIsoBigFactorization B T S f ≪≫
    Functor.isoWhiskerRight
      (smallEtaleToBigEtaleMorphism_comp_pushforwardIso B T S f).symm
      (bigEtaleToSmallEtaleMorphism B S.obj S.property).pushforward

add_to_stacks 021I "small_site_pushforward"
  CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj

end AlgebraicGeometry
