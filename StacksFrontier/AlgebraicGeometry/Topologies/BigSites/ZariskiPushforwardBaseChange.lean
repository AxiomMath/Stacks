module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiFactorization
public import StacksFrontier.CategoryTheory.Sites.Localization.MoreLocalization

/-!
# Base change for direct images on the Zariski sites

For a cartesian square of schemes in a big Zariski site, direct image from the big site over
the top commutes both with inverse image on the big sites and with restriction to the small
sites. Both comparisons are natural in the sheaf.

## Main results

* `AlgebraicGeometry.bigZariskiBaseChange_pushforwardIso` — big-site base change.
* `AlgebraicGeometry.smallZariskiBaseChange_pushforwardIso` — restricting a big-site direct
  image to the small site of `S'` is restricting to the small site of `T'` followed by the
  small-site direct image.

## Implementation notes

Both statements are isomorphisms rather than equalities of functors, because the small-site
base-change functor is pinned down only up to a canonical isomorphism with fibre product.

The big-site statement is Mathlib's base-change comparison for the localizations of one
Grothendieck topology, which applies once the topology of the big Zariski site over a scheme
is identified with the localization of the ambient topology
(`AlgebraicGeometry.BigZariskiOver.topology_eq_over`); the two `heq` lemmas transport the
sheaf pushforward and pullback along that identification. The small-site statement is then
obtained by factoring restriction to a small site through the big site over the same scheme,
which is `smallToBig_inverseImage_factor`.

## References

* [Stacks Project, Tag 0DD9](https://stacks.math.columbia.edu/tag/0DD9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private theorem sheafPushforwardCocontinuous_heq
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (A : Type*) [Category A]
    {J J' : GrothendieckTopology C} {K K' : GrothendieckTopology D}
    [F.IsCocontinuous J K] [F.IsCocontinuous J' K']
    [∀ G : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension G]
    (hJ : J = J') (hK : K = K') :
    F.sheafPushforwardCocontinuous A J K ≍
      F.sheafPushforwardCocontinuous A J' K' := by
  cases hJ
  cases hK
  rfl

private theorem sheafPullbackCocontinuous_heq
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (A : Type*) [Category A]
    {J J' : GrothendieckTopology C} {K K' : GrothendieckTopology D}
    [HasWeakSheafify J A] [HasWeakSheafify J' A]
    (hJ : J = J') (hK : K = K') :
    F.sheafPullbackCocontinuous A J K ≍
      F.sheafPullbackCocontinuous A J' K' := by
  cases hJ
  cases hK
  rfl

private noncomputable def smallToBig_inverseImage_factor
    (B : BigZariskiSite.{u}) {T S : B.Schemes} (f : T ⟶ S) :
    (smallZariskiToBigZariskiMorphism B T S f).inverseImage ≅
      (bigZariskiMorphism B T S f).inverseImage ⋙
        (smallZariskiProjection B T).pushforward := by
  let U := SmallZariski.inclusion B T.1 T.property
  let V := Over.map f
  let W := smallZariskiToBigZariskiFunctor B T S f
  let J := SmallZariski.topology B T.1 T.property
  let K := BigZariskiOver.topology B T.1 T.property
  let L := BigZariskiOver.topology B S.1 S.property
  let : U.IsContinuous J K := smallZariskiInclusion_isContinuous B T
  let : V.IsContinuous K L := bigZariskiMap_isContinuous B T S f
  let : (U ⋙ V).IsContinuous J L := Functor.isContinuous_comp U V J K L
  let : W.IsCocontinuous J L :=
    smallZariskiToBigZariskiFunctor_isCocontinuous B T S f
  let : W.IsContinuous J L :=
    smallZariskiToBigZariskiFunctor_isContinuous B T S f
  let αW := W.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) J L
  let αV := V.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) K L
  simpa [smallZariskiToBigZariskiMorphism, bigZariskiMorphism,
    smallZariskiProjection, W, U, V, J, K, L] using
      (αW.trans (Functor.sheafPushforwardContinuousComp U V (Type (u + 1)) J K L).symm ≪≫
        Functor.isoWhiskerRight αV.symm
          (U.sheafPushforwardContinuous (Type (u + 1)) J K))

private noncomputable def smallZariskiProjection_pushforward_baseChangeIso
    (B : BigZariskiSite.{u}) {T S : B.Schemes} (f : T ⟶ S) :
    (smallZariskiProjection B T).pushforward ⋙
        (smallZariskiMorphism B T S f).pushforward ≅
      (bigZariskiMorphism B T S f).pushforward ⋙
        (smallZariskiProjection B S).pushforward := by
  let πT := smallZariskiProjection B T
  let πS := smallZariskiProjection B S
  let F := smallZariskiMorphism B T S f
  let G := bigZariskiMorphism B T S f
  exact Adjunction.rightAdjointUniq
    ((F.adj.comp πT.adj).ofNatIsoLeft (by
      simpa [F, πT, G, πS, MorphismOfTopoi.comp] using
        smallZariskiProjection_baseChangeIso B T S f))
    (πS.adj.comp G.adj)

variable (B : BigZariskiSite.{u})
variable {T' T S' S : B.Schemes}
variable (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)

/-- Big-site inverse image commutes with big-site direct image around a
cartesian square, naturally in the sheaf. -/
@[stacks 0DD9 "big-site equality"]
public noncomputable def bigZariskiBaseChange_pushforwardIso
    (h : IsPullback g' f' f g) :
    (bigZariskiMorphism B T S f).pushforward ⋙
        (bigZariskiMorphism B S' S g).inverseImage ≅
      (bigZariskiMorphism B T' T g').inverseImage ⋙
        (bigZariskiMorphism B T' S' f').pushforward := Classical.choice (by
  refine ⟨?_⟩
  let J := B.grothendieckTopology
  have hT : BigZariskiOver.topology B T.1 T.property = J.over T := by
    simpa [J] using BigZariskiOver.topology_eq_over B T
  have hS : BigZariskiOver.topology B S.1 S.property = J.over S := by
    simpa [J] using BigZariskiOver.topology_eq_over B S
  have hT' : BigZariskiOver.topology B T'.1 T'.property = J.over T' := by
    simpa [J] using BigZariskiOver.topology_eq_over B T'
  have hS' : BigZariskiOver.topology B S'.1 S'.property = J.over S' := by
    simpa [J] using BigZariskiOver.topology_eq_over B S'
  let e := J.overMapPushforwardBaseChange (Type (u + 1)) h.toCommSq
  haveI : IsIso e.natTrans := J.isIso_overMapPushforwardBaseChange
    (Type (u + 1)) h
  let αg := (Over.map g).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) (J.over S') (J.over S)
  let αg' := (Over.map g').sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) (J.over T') (J.over T)
  convert (Functor.isoWhiskerLeft
        ((Over.map f).sheafPushforwardCocontinuous (Type (u + 1)) (J.over T) (J.over S)) αg ≪≫
      asIso e.natTrans ≪≫
      Functor.isoWhiskerRight αg'.symm
        ((Over.map f').sheafPushforwardCocontinuous (Type (u + 1)) (J.over T') (J.over S'))) using 1
  all_goals
    congr 30
    all_goals
      try simp only [bigZariskiMorphism]
      first
      | exact sheafPushforwardCocontinuous_heq (F := Over.map f) (A := Type (u + 1))
          (J := BigZariskiOver.topology B T.1 T.property) (J' := J.over T)
          (K := BigZariskiOver.topology B S.1 S.property) (K' := J.over S) hT hS
      | exact sheafPullbackCocontinuous_heq (F := Over.map g) (A := Type (u + 1))
          (J := BigZariskiOver.topology B S'.1 S'.property) (J' := J.over S')
          (K := BigZariskiOver.topology B S.1 S.property) (K' := J.over S) hS' hS
      | exact sheafPullbackCocontinuous_heq (F := Over.map g') (A := Type (u + 1))
          (J := BigZariskiOver.topology B T'.1 T'.property) (J' := J.over T')
          (K := BigZariskiOver.topology B T.1 T.property) (K' := J.over T) hT' hT
      | exact sheafPushforwardCocontinuous_heq (F := Over.map f') (A := Type (u + 1))
          (J := BigZariskiOver.topology B T'.1 T'.property) (J' := J.over T')
          (K := BigZariskiOver.topology B S'.1 S'.property) (K' := J.over S') hT' hS')

private noncomputable def smallZariskiBaseChange_pushforwardIso_aux
    (B : BigZariskiSite.{u}) {T' T S' S : B.Schemes}
    (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) :
    (bigZariskiMorphism B T S f).pushforward ⋙
        (smallZariskiToBigZariskiMorphism B S' S g).inverseImage ≅
      (smallZariskiToBigZariskiMorphism B T' T g').inverseImage ⋙
        (smallZariskiMorphism B T' S' f').pushforward := by
  let F := bigZariskiMorphism B T S f
  let G := bigZariskiMorphism B S' S g
  let G' := bigZariskiMorphism B T' T g'
  let F' := bigZariskiMorphism B T' S' f'
  let H := smallZariskiMorphism B T' S' f'
  let πS' := smallZariskiProjection B S'
  let πT' := smallZariskiProjection B T'
  let h_g := smallToBig_inverseImage_factor B g
  let h_g' := smallToBig_inverseImage_factor B g'
  let h_small := smallZariskiProjection_pushforward_baseChangeIso B f'
  calc
    F.pushforward ⋙
        (smallZariskiToBigZariskiMorphism B S' S g).inverseImage ≅
      F.pushforward ⋙ (G.inverseImage ⋙ πS'.pushforward) :=
        Functor.isoWhiskerLeft F.pushforward h_g
    _ ≅ (F.pushforward ⋙ G.inverseImage) ⋙ πS'.pushforward :=
      (Functor.associator _ _ _).symm
    _ ≅ (G'.inverseImage ⋙ F'.pushforward) ⋙ πS'.pushforward :=
      Functor.isoWhiskerRight (bigZariskiBaseChange_pushforwardIso B g' f' f g h)
        πS'.pushforward
    _ ≅ G'.inverseImage ⋙ (F'.pushforward ⋙ πS'.pushforward) :=
      Functor.associator _ _ _
    _ ≅ G'.inverseImage ⋙ (πT'.pushforward ⋙ H.pushforward) :=
      Functor.isoWhiskerLeft G'.inverseImage h_small.symm
    _ ≅ (G'.inverseImage ⋙ πT'.pushforward) ⋙ H.pushforward :=
      Functor.associator _ _ _
    _ ≅ (smallZariskiToBigZariskiMorphism B T' T g').inverseImage ⋙
        H.pushforward :=
      Functor.isoWhiskerRight h_g'.symm H.pushforward

/-- Restricting a big-site direct image to the small site of `S'` agrees,
naturally, with restricting to the small site of `T'` and taking the small-site
direct image. -/
@[stacks 0DD9 "small-site equality"]
public noncomputable def smallZariskiBaseChange_pushforwardIso
    (h : IsPullback g' f' f g) :
    (bigZariskiMorphism B T S f).pushforward ⋙
        (smallZariskiToBigZariskiMorphism B S' S g).inverseImage ≅
      (smallZariskiToBigZariskiMorphism B T' T g').inverseImage ⋙
        (smallZariskiBaseChange B f').sheafPushforwardContinuous
          (Type (u + 1))
          (SmallZariski.topology B S'.1 S'.property)
          (SmallZariski.topology B T'.1 T'.property) := Classical.choice (by
  refine ⟨?_⟩
  simpa [smallZariskiMorphism] using
    smallZariskiBaseChange_pushforwardIso_aux B g' f' f g h)

end AlgebraicGeometry
