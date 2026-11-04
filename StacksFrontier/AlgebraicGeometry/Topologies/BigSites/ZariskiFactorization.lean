module

public import Mathlib.CategoryTheory.Whiskering
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiCovering.BigZariskiMorphism
public import StacksFrontier.CategoryTheory.Sites.RelocalizationMorphism

/-!
# Naturality of the small and big Zariski topoi in the base

Let `f : T ⟶ S` be a morphism in a big Zariski site. The four geometric morphisms relating
the small and big Zariski topoi of `T` and of `S` form a commutative square

`f_small ∘ π_T = π_S ∘ f_big`,

and the morphism `i_f` from the small topos of `T` to the big topos over `S` factors as
`f_big ∘ i_T`. Combining the two, `f_small` is `π_S ∘ i_f`, and also
`π_S ∘ f_big ∘ i_T`.

## Main definitions

* `AlgebraicGeometry.smallZariskiMorphism` — the geometric morphism `f_small` of small Zariski
  topoi induced by small-site base change.

## Main results

* `AlgebraicGeometry.smallZariskiBaseChange_comp_inclusionIso` — the square of site functors
  commutes, naturally in the small-site object.
* `AlgebraicGeometry.smallZariskiProjection_baseChangeIso` — the square of geometric morphisms
  commutes.
* `AlgebraicGeometry.smallZariskiToBigZariskiMorphism_factor_pushforwardIso` and
  `AlgebraicGeometry.smallZariskiToBigZariskiMorphism_factor_inverseImageIso` — the
  factorization of `i_f`.
* `AlgebraicGeometry.smallZariskiMorphismIsoProjectionCompBig` and
  `AlgebraicGeometry.smallZariskiMorphismIsoProjectionCompInclusion` — the two factorizations
  of `f_small`.

## Implementation notes

The site-level square commutes only up to a natural isomorphism, not on the nose: the
small-site base-change functor is pinned down only up to a canonical isomorphism with
scheme-theoretic fibre product, so the comparison is obtained by cancelling the fully faithful
functor from the small site into the slice of schemes.

Equality of geometric morphisms is expressed throughout as a natural isomorphism of their
inverse-image functors, or of their direct images; the two are interchangeable because the
adjoints of isomorphic functors are isomorphic, which is what
`CategoryTheory.Adjunction.leftAdjointUniq` and `rightAdjointUniq` supply.

## References

* [Stacks Project, Tag 0211](https://stacks.math.columbia.edu/tag/0211)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry


variable (B : BigZariskiSite.{u}) (T S : B.Schemes) (f : T ⟶ S)

/-- The geometric morphism induced by small-site base change. -/
public noncomputable def smallZariskiMorphism :
    MorphismOfTopoi
      (Sheaf (SmallZariski.topology B T.1 T.property) (Type (u + 1)))
      (Sheaf (SmallZariski.topology B S.1 S.property) (Type (u + 1))) :=
  let h := (smallZariskiBaseChange_isMorphismOfSites B f).hasExactLeftAdjoint
  { pushforward := (smallZariskiBaseChange B f).sheafPushforwardContinuous
      (Type (u + 1)) (SmallZariski.topology B S.1 S.property)
      (SmallZariski.topology B T.1 T.property)
    inverseImage := Classical.choose h
    adj := Classical.choice (Classical.choose_spec h).1
    preservesFiniteLimits := (Classical.choose_spec h).2 }

/-- The square of functors underlying the four morphisms of Zariski sites
commutes up to a natural isomorphism. -/
@[stacks 0211 "commutative_square"]
public noncomputable def smallZariskiBaseChange_comp_inclusionIso :
    smallZariskiBaseChange B f ⋙
        SmallZariski.inclusion B T.1 T.property ≅
      SmallZariski.inclusion B S.1 S.property ⋙ Over.pullback f := by
  let P := Over.post (X := T) B.inclusion
  let hI : B.inclusion.FullyFaithful := by
    change (ObjectProperty.ι (fun X : Scheme.{u} => X.size < B.schemeCardinal)).FullyFaithful
    exact ObjectProperty.fullyFaithfulι _
  let hP : P.FullyFaithful := Functor.FullyFaithful.over T B.inclusion hI
  let e := smallZariskiBaseChangeIso B f
  let e' := (Over.postPullbackIso B.inclusion f).symm
  have hpost :
      (smallZariskiBaseChange B f ⋙
        SmallZariski.inclusion B T.1 T.property) ⋙ P ≅
      (SmallZariski.inclusion B S.1 S.property ⋙ Over.pullback f) ⋙ P := by
    simpa [P, smallSiteInSchemesOver] using
      (Functor.associator _ _ _).trans <|
        e.trans <| (Functor.associator _ _ _).trans <|
          (Functor.isoWhiskerLeft (SmallZariski.inclusion B S.1 S.property) e').trans <|
            (Functor.associator _ _ _).symm
  let := hP.full
  let := hP.faithful
  exact Functor.fullyFaithfulCancelRight P hpost

/-- The geometric morphisms satisfy `f_small ∘ π_T ≅ π_S ∘ f_big`;
the isomorphism of inverse-image functors is natural in sheaves. -/
@[stacks 0211 "commutative_square"]
public noncomputable def smallZariskiProjection_baseChangeIso :
    ((smallZariskiMorphism B T S f).comp
      (smallZariskiProjection B T)).inverseImage ≅
    ((smallZariskiProjection B S).comp
      (bigZariskiMorphism B T S f)).inverseImage := by
  let F := smallZariskiBaseChange B f
  let iT := SmallZariski.inclusion B T.1 T.property
  let iS := SmallZariski.inclusion B S.1 S.property
  let q := Over.pullback f
  let JS := SmallZariski.topology B S.1 S.property
  let JT := SmallZariski.topology B T.1 T.property
  let KS := BigZariskiOver.topology B S.1 S.property
  let KT := BigZariskiOver.topology B T.1 T.property
  let eSite := smallZariskiBaseChange_comp_inclusionIso B T S f
  let : iT.IsContinuous JT KT := smallZariskiInclusion_isContinuous B T
  let : iS.IsContinuous JS KS := smallZariskiInclusion_isContinuous B S
  let : q.IsContinuous KS KT := bigZariskiPullback_isContinuous B T S f
  let : (F ⋙ iT).IsContinuous JS KT :=
    Functor.isContinuous_comp F iT JS JT KT
  let : (iS ⋙ q).IsContinuous JS KT :=
    Functor.isContinuous_comp iS q JS KS KT
  have hcomposite :
      iT.sheafPushforwardContinuous (Type (u + 1)) JT KT ⋙
          F.sheafPushforwardContinuous (Type (u + 1)) JS JT ≅
        q.sheafPushforwardContinuous (Type (u + 1)) KS KT ⋙
          iS.sheafPushforwardContinuous (Type (u + 1)) JS KS :=
    (Functor.sheafPushforwardContinuousComp F iT (Type (u + 1)) JS JT KT).trans <|
      (Functor.sheafPushforwardContinuousIso eSite (Type (u + 1)) JS KT).trans <|
        (Functor.sheafPushforwardContinuousComp iS q (Type (u + 1)) JS KS KT).symm
  have hpush :
      (bigZariskiMorphism B T S f).pushforward ⋙
          (smallZariskiProjection B S).pushforward ≅
        (smallZariskiProjection B T).pushforward ⋙
          (smallZariskiMorphism B T S f).pushforward := by
    change
      (Over.map f).sheafPushforwardCocontinuous (Type (u + 1)) KT KS ⋙
          iS.sheafPushforwardContinuous (Type (u + 1)) JS KS ≅
        iT.sheafPushforwardContinuous (Type (u + 1)) JT KT ⋙
          F.sheafPushforwardContinuous (Type (u + 1)) JS JT
    exact (Functor.isoWhiskerRight
        ((Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type (u + 1)))
        (iS.sheafPushforwardContinuous (Type (u + 1)) JS KS)).trans hcomposite.symm
  exact (((smallZariskiMorphism B T S f).adj.comp
      (smallZariskiProjection B T).adj).leftAdjointUniq
      (((smallZariskiProjection B S).adj.comp
        (bigZariskiMorphism B T S f).adj).ofNatIsoRight hpush))



variable (B : BigZariskiSite.{u}) (T S : B.Schemes) (f : T ⟶ S)

/-- The direct image of `i_f` agrees naturally with that of `f_big ∘ i_T`. -/
@[stacks 0211 "if_factorization"]
public noncomputable def smallZariskiToBigZariskiMorphism_factor_pushforwardIso :
    (smallZariskiToBigZariskiMorphism B T S f).pushforward ≅
      ((bigZariskiMorphism B T S f).comp
        (smallZariskiToBigZariskiMorphism B T T (𝟙 T))).pushforward := by
  let U := smallZariskiToBigZariskiFunctor B T T (𝟙 T)
  let V := Over.map f
  let J := SmallZariski.topology B T.obj T.property
  let K := BigZariskiOver.topology B T.obj T.property
  let L := BigZariskiOver.topology B S.obj S.property
  let A := Type (u + 1)
  let iJ := sheafToPresheaf J A
  let iK := sheafToPresheaf K A
  let iL := sheafToPresheaf L A
  let uStar := U.sheafPushforwardCocontinuous A J K
  let vStar := V.sheafPushforwardCocontinuous A K L
  have hfun : U ⋙ V = smallZariskiToBigZariskiFunctor B T S f := by
    dsimp [U, V, smallZariskiToBigZariskiFunctor]
    rw [Functor.assoc, ← Over.mapComp_eq, Category.id_comp]
  let : (U ⋙ V).IsCocontinuous J L :=
    hfun ▸ (smallZariskiToBigZariskiFunctor_isCocontinuous B T S f)
  have hleft :=
    (Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso
      (G := U ⋙ V) (A := A) (J := J) (K := L)).trans
      (Functor.isoWhiskerLeft iJ (Adjunction.rightAdjointUniq
        (Functor.ranAdjunction (U.op ⋙ V.op) (Type (u + 1)))
        ((Functor.ranAdjunction V.op (Type (u + 1))).comp
          (Functor.ranAdjunction U.op (Type (u + 1))))))
  have hright : (uStar ⋙ vStar) ⋙ iL ≅ iJ ⋙ U.op.ran ⋙ V.op.ran := by
    calc
      (uStar ⋙ vStar) ⋙ iL ≅ uStar ⋙ (vStar ⋙ iL) := Functor.associator _ _ _
      _ ≅ uStar ⋙ (iK ⋙ V.op.ran) :=
        Functor.isoWhiskerLeft _
          (Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso
            (G := V) (A := A) (J := K) (K := L))
      _ ≅ (uStar ⋙ iK) ⋙ V.op.ran := (Functor.associator _ _ _).symm
      _ ≅ (iJ ⋙ U.op.ran) ⋙ V.op.ran :=
        Functor.isoWhiskerRight
          (Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso
            (G := U) (A := A) (J := J) (K := K)) _
      _ ≅ iJ ⋙ U.op.ran ⋙ V.op.ran := Functor.associator _ _ _
  have hcomp := Functor.fullyFaithfulCancelRight iL (hleft.trans hright.symm)
  simpa [smallZariskiToBigZariskiFunctor, smallZariskiToBigZariskiMorphism,
    bigZariskiMorphism, MorphismOfTopoi.comp, Functor.assoc, hfun,
    ← Over.mapComp_eq, Category.id_comp] using hcomp

/-- The inverse image of `i_f` agrees naturally with that of `f_big ∘ i_T`. -/
@[stacks 0211 "if_factorization"]
public noncomputable def smallZariskiToBigZariskiMorphism_factor_inverseImageIso :
    (smallZariskiToBigZariskiMorphism B T S f).inverseImage ≅
      ((bigZariskiMorphism B T S f).comp
        (smallZariskiToBigZariskiMorphism B T T (𝟙 T))).inverseImage :=
  (Adjunction.leftAdjointCompIso
    (bigZariskiMorphism B T S f).adj
    (smallZariskiToBigZariskiMorphism B T T (𝟙 T)).adj
    (smallZariskiToBigZariskiMorphism B T S f).adj
    (smallZariskiToBigZariskiMorphism_factor_pushforwardIso B T S f).symm).symm



variable (B : BigZariskiSite.{u}) (T S : B.Schemes) (f : T ⟶ S)

/-- The small-site morphism factors through the two big Zariski topoi. -/
@[stacks 0211 "small_factorization"]
public noncomputable def smallZariskiMorphismIsoProjectionCompBig :
    (smallZariskiMorphism B T S f).inverseImage ≅
      ((smallZariskiProjection B S).comp
        ((bigZariskiMorphism B T S f).comp
          (smallZariskiToBigZariskiMorphism B T T (𝟙 T)))).inverseImage := by
  let h := smallZariskiProjection_baseChangeIso B T S f
  let r := smallZariskiProjection_comp_identity B T
  calc
    (smallZariskiMorphism B T S f).inverseImage ≅
        (smallZariskiMorphism B T S f).inverseImage ⋙ 𝟭 _ :=
      (Functor.rightUnitor _).symm
    _ ≅ (smallZariskiMorphism B T S f).inverseImage ⋙
        ((smallZariskiProjection B T).inverseImage ⋙
          (smallZariskiToBigZariskiMorphism B T T (𝟙 T)).inverseImage) := by
      simpa [MorphismOfTopoi.comp] using
        Functor.isoWhiskerLeft (smallZariskiMorphism B T S f).inverseImage r.symm
    _ ≅ (((smallZariskiMorphism B T S f).inverseImage ⋙
        (smallZariskiProjection B T).inverseImage) ⋙
          (smallZariskiToBigZariskiMorphism B T T (𝟙 T)).inverseImage) :=
      (Functor.associator _ _ _).symm
    _ ≅ (((smallZariskiProjection B S).inverseImage ⋙
        (bigZariskiMorphism B T S f).inverseImage) ⋙
          (smallZariskiToBigZariskiMorphism B T T (𝟙 T)).inverseImage) := by
      simpa [MorphismOfTopoi.comp] using
        (Functor.isoWhiskerRight h
          (smallZariskiToBigZariskiMorphism B T T (𝟙 T)).inverseImage)

/-- The same morphism factors through `i_f` and the projection at `S`. -/
@[stacks 0211 "small_factorization"]
public noncomputable def smallZariskiMorphismIsoProjectionCompInclusion :
    (smallZariskiMorphism B T S f).inverseImage ≅
      ((smallZariskiProjection B S).comp
        (smallZariskiToBigZariskiMorphism B T S f)).inverseImage := by
  let h := smallZariskiToBigZariskiMorphism_factor_inverseImageIso B T S f
  calc
    (smallZariskiMorphism B T S f).inverseImage ≅
        ((smallZariskiProjection B S).comp
          ((bigZariskiMorphism B T S f).comp
            (smallZariskiToBigZariskiMorphism B T T (𝟙 T)))).inverseImage :=
      smallZariskiMorphismIsoProjectionCompBig B T S f
    _ ≅ ((smallZariskiProjection B S).comp
        (smallZariskiToBigZariskiMorphism B T S f)).inverseImage := by
      change
        (smallZariskiProjection B S).inverseImage ⋙
            ((bigZariskiMorphism B T S f).comp
              (smallZariskiToBigZariskiMorphism B T T (𝟙 T))).inverseImage ≅
          (smallZariskiProjection B S).inverseImage ⋙
            (smallZariskiToBigZariskiMorphism B T S f).inverseImage
      exact (Functor.isoWhiskerLeft
        (smallZariskiProjection B S).inverseImage h).symm

end AlgebraicGeometry
