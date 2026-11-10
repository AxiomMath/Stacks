module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSchemeSourceRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeEtaleFamily
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCompositionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlasRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange

/-!
# Being locally of finite type is local on the source and the target

For a morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S`, being locally of finite
type descends along a surjective representable étale morphism `U ⟶ X`, and for formal algebraic
spaces `X`, `Y` it is equivalent to the square and atlas conditions of Stacks 0ANL.

## Main results

* `IsLocallyOfFiniteType.of_comp_of_locallySurjective`: If `p : U ⟶ X` is representable étale
  and surjective and `p ≫ f` is locally of finite type, then `f` is locally of finite type.
* `isLocallyOfFiniteTypeOnEverySquare_of_isLocallyOfFiniteType`: A morphism locally of finite
  type is locally of finite type on every commutative square of representable étale charts.
* `isLocallyOfFiniteType_of_onSomeSquare`: A morphism locally of finite type on some square with
  surjective source chart is locally of finite type.
* `isLocallyOfFiniteTypeAfterTargetCover_of_onEverySquare'`,
  `isLocallyOfFiniteTypeOnFactoredAtlas_of_afterTargetCover'`,
  `isLocallyOfFiniteType_of_onFactoredAtlas`: The implications (3) ⇒ (4) ⇒ (5) ⇒ (1) of
  Stacks 0ANL.
* `isLocallyOfFiniteType_tfae_squares`: For formal algebraic spaces, being locally of finite
  type, being so on some square and being so on every square are equivalent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If `p ≫ f = t ≫ q` with `t` locally of finite type and `q` representable étale, then
`p ≫ f` is locally of finite type. -/
private theorem isLocallyOfFiniteType_comp_of_comm {X Y Z W : FppfSheaf B S hS} {p : W ⟶ X}
    {f : X ⟶ Y} {t : W ⟶ Z} {q : Z ⟶ Y} (hcomm : p ≫ f = t ≫ q)
    (ht : IsLocallyOfFiniteType B S hS t) (hq : IsRepresentableEtale B S hS q) :
    IsLocallyOfFiniteType B S hS (p ≫ f) :=
  hcomm ▸ IsLocallyOfFiniteType.comp B S hS t q ht
    (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS q hq)

/-- A morphism `f : X ⟶ Y` locally of finite type is locally of finite type on every square: for
representable étale `p : U ⟶ X` and `q : V ⟶ Y` from formal algebraic spaces and `t : U ⟶ V`
with `p ≫ f = t ≫ q`, the map `t` is locally of finite type. -/
@[stacks 0ANL "condition (1) implies condition (3)"]
theorem isLocallyOfFiniteTypeOnEverySquare_of_isLocallyOfFiniteType {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteTypeOnEverySquare B S hS f := by
  intro U V p q t _ hV hp _ hcomm
  have hpf : IsLocallyOfFiniteType B S hS (p ≫ f) :=
    IsLocallyOfFiniteType.comp B S hS p f
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS p hp) hf
  rw [hcomm] at hpf
  exact IsLocallyOfFiniteType.of_comp B S hS t q hV hpf

/-- If `f : X ⟶ Y` is locally of finite type after a target cover, then it is locally of finite
type on a factored atlas: there is an affine étale covering of `X` each member of which factors
through an affine formal algebraic space representable étale over `Y` by a map locally of finite
type. -/
@[stacks 0ANL "condition (4) implies condition (5)"]
theorem isLocallyOfFiniteTypeOnFactoredAtlas_of_afterTargetCover' {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteTypeAfterTargetCover B S hS f) :
    IsLocallyOfFiniteTypeOnFactoredAtlas B S hS f := by
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨J, V, v, hVcover, hcharts⟩ := hf
  choose I U w hUcover hUfinite using hcharts
  refine ⟨Σ j, I j, fun ji ↦ U ji.1 ji.2, fun ji ↦ w ji.1 ji.2 ≫ pullback.snd (v ji.1) f,
    ⟨fun ji ↦ (hUcover ji.1).1 ji.2, fun ji ↦ IsRepresentableEtale.comp B S hS
      ((hUcover ji.1).2.1 ji.2)
      (isRepresentableEtale_pullback_snd B S hS (v ji.1) f (hVcover.2.1 ji.1)),
    isLocallySurjective_sigmaDesc_comp' B S hS (fun j ↦ pullback.snd (v j) f) w
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hVcover.2.2)
      fun j ↦ (hUcover j).2.2⟩, fun ji ↦ ?_⟩
  refine ⟨V ji.1, v ji.1, w ji.1 ji.2 ≫ pullback.fst (v ji.1) f, hVcover.1 ji.1,
    hVcover.2.1 ji.1, ?_, hUfinite ji.1 ji.2⟩
  simp [pullback.condition]

/-- Let `X`, `Y` be formal algebraic spaces. If `f : X ⟶ Y` is locally of finite type on every
square, then it is locally of finite type after a target cover: there is an affine étale
covering `{Vⱼ ⟶ Y}` and, for each `j`, an affine étale covering of `Vⱼ ×_Y X` whose members are
locally of finite type over `Vⱼ`. -/
@[stacks 0ANL "condition (3) implies condition (4)"]
theorem isLocallyOfFiniteTypeAfterTargetCover_of_onEverySquare' {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteTypeOnEverySquare B S hS f) :
    IsLocallyOfFiniteTypeAfterTargetCover B S hS f := by
  obtain ⟨-, J, V, v, hVaffine, hVetale, hVsurj⟩ := id hY
  refine ⟨J, V, v, ⟨hVaffine, hVetale, hVsurj⟩, fun j ↦ ?_⟩
  obtain ⟨-, I, U, w, hUaffine, hUetale, hUsurj⟩ :=
    isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS (v j) f hY
      (hVaffine j) hX
  refine ⟨I, U, w, ⟨hUaffine, hUetale, hUsurj⟩, fun i ↦ ?_⟩
  refine hf (U i) (V j) (w i ≫ pullback.snd (v j) f) (v j) (w i ≫ pullback.fst (v j) f)
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hUaffine i))
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hVaffine j))
    (IsRepresentableEtale.comp B S hS (hUetale i)
      (isRepresentableEtale_pullback_snd B S hS (v j) f (hVetale j)))
    (hVetale j) (by simp [pullback.condition])

/-! ### Being locally of finite type is local on the source -/

/-- **Being locally of finite type is local on the source.** Let `f : X ⟶ Y` be a morphism of
fppf sheaves on the big fppf site of `S` and let `p : U ⟶ X` be representable étale and
surjective as a morphism of sheaves. If `p ≫ f` is locally of finite type then so is `f`. -/
theorem IsLocallyOfFiniteType.of_comp_of_locallySurjective {X Y U : FppfSheaf B S hS}
    (f : X ⟶ Y) (p : U ⟶ X) (hp : IsRepresentableEtale B S hS p)
    (hsurj : Sheaf.IsLocallySurjective p)
    (hpf : IsLocallyOfFiniteType B S hS (p ≫ f)) :
    IsLocallyOfFiniteType B S hS f := by
  obtain ⟨hcrep, hcprop⟩ := hpf
  have hrepf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
    isRepresentableByAlgebraicSpacesULift_of_comp_of_locallySurjective B S hS f p hp hsurj hcrep
  refine ⟨hrepf, fun T ξ ↦ ?_⟩
  change Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (pullback.fst ξ f.hom)
  obtain ⟨Z, β, hβE, hcs, hce⟩ :=
    exists_schemeChart_pullback_of_locallySurjective B S hS f p hp hsurj hcrep T ξ
  have hfac : pullback.fst (pullback.snd ξ f.hom) p.hom ≫ pullback.fst ξ f.hom =
      (pullbackLeftPullbackSndIso ξ f.hom p.hom).hom ≫
        pullback.fst ξ (p.hom ≫ f.hom) := by
    simp
  have hlft : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
      (pullback.fst (pullback.snd ξ f.hom) p.hom ≫ pullback.fst ξ f.hom) := by
    rw [hfac]
    exact Space.holdsOnEveryEtaleChartULift_precomp B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u}) _ _ (hcprop T ξ)
  have hchart : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      ((uliftYoneda.{u + 1}).preimage
        ((β ≫ pullback.fst (pullback.snd ξ f.hom) p.hom) ≫ pullback.fst ξ f.hom))) := by
    refine hlft Z T β (𝟙 _) _ hβE (Space.relative_id_etale.{u + 1} B S hS T) ?_
    rw [Category.comp_id, Functor.map_preimage, Category.assoc]
  refine Space.holdsOnEveryEtaleChartULift_of_surjectiveChart B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (hrepf T ξ)
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T) Z T
    (β ≫ pullback.fst (pullback.snd ξ f.hom) p.hom) (𝟙 _) _ hce
    (Space.relative_id_etale.{u + 1} B S hS T) hcs ?_ hchart
  rw [Category.comp_id, Functor.map_preimage]

/-- A morphism `f : X ⟶ Y` which is locally of finite type on some square is locally of finite
type: it suffices that `p ≫ f = t ≫ q` for a surjective representable étale `p : U ⟶ X`, a
representable étale `q : V ⟶ Y` from formal algebraic spaces and `t : U ⟶ V` locally of finite
type. -/
@[stacks 0ANL "condition (2) implies condition (1), reading surjectivity of the source column \
as surjectivity of the morphism of sheaves"]
theorem isLocallyOfFiniteType_of_onSomeSquare {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteTypeOnSomeSquare B S hS f) :
    IsLocallyOfFiniteType B S hS f := by
  obtain ⟨U, V, p, q, t, -, -, hp, hpsurj, hq, ht, hcomm⟩ := hf
  exact IsLocallyOfFiniteType.of_comp_of_locallySurjective B S hS f p hp hpsurj
    (isLocallyOfFiniteType_comp_of_comm B S hS hcomm ht hq)

/-- Let `X`, `Y` be formal algebraic spaces and `f : X ⟶ Y`. If there is an affine étale
covering `{Uᵢ ⟶ X}` each member of which factors as `Uᵢ ⟶ Vᵢ ⟶ Y` through an affine formal
algebraic space representable étale over `Y` by a map locally of finite type, then `f` is
locally of finite type. -/
@[stacks 0ANL "condition (5) implies condition (1), reading the covering of Definition 0AIM \
as a jointly surjective family of morphisms of sheaves"]
theorem isLocallyOfFiniteType_of_onFactoredAtlas {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteTypeOnFactoredAtlas B S hS f) :
    IsLocallyOfFiniteType B S hS f := by
  obtain ⟨I, U, u, hcover, hfac⟩ := hf
  refine IsLocallyOfFiniteType.of_etaleFamily B S hS f hX.1 hY u hcover.2.1 hcover.2.2
    fun i ↦ ?_
  obtain ⟨V, v, t, -, hv, hcomm, ht⟩ := hfac i
  exact isLocallyOfFiniteType_comp_of_comm B S hS hcomm ht hv

/-- For a morphism `f : X ⟶ Y` of formal algebraic spaces, the following are equivalent: `f` is
locally of finite type; `f` is locally of finite type on some square; `f` is locally of finite
type on every square. -/
@[stacks 0ANL "the equivalence of conditions (1), (2) and (3)"]
theorem isLocallyOfFiniteType_tfae_squares {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) :
    List.TFAE [IsLocallyOfFiniteType B S hS f,
      IsLocallyOfFiniteTypeOnSomeSquare B S hS f,
      IsLocallyOfFiniteTypeOnEverySquare B S hS f] := by
  tfae_have 1 → 2 := isLocallyOfFiniteTypeOnSomeSquare_of_isLocallyOfFiniteType B S hS f hX hY
  tfae_have 2 → 1 := isLocallyOfFiniteType_of_onSomeSquare B S hS f
  tfae_have 1 → 3 := isLocallyOfFiniteTypeOnEverySquare_of_isLocallyOfFiniteType B S hS f
  tfae_have 3 → 1 := isLocallyOfFiniteType_of_onEverySquare B S hS f hX hY
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
