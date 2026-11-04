module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasFiniteSubcover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSchemeSourceRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismFlatCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves

/-!
# Quasi-compact formal algebraic spaces: Stacks 0AJ9 without its stand-in hypotheses

`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria` states the equivalence of
the three conditions of **Stacks 0AJ9** on hypotheses standing for the steps of the omitted
proof: `hAffineReduction` and `hReductionEtaleSurjective` for the implication (3) ⇒ (1), and
`hFiniteRefinement` for the implication (1) ⇒ (2). This file proves those steps, using two
results of `StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaRefined`:
`AlgebraicGeometry.FormalSpace.affineReductionsQuasiCompact`, that the reduction of an affine
formal algebraic space is quasi-compact, and
`AlgebraicGeometry.FormalSpace.hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_reduction`, the
implication (1) ⇒ (2).

* `AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace.isQuasiCompactSpaceULift_of_isReduction`:
  the implication (3) ⇒ (1), unconditionally: for a quasi-compact surjective étale chart
  `Y ⟶ X`, the fibre product `Y ×_X Xred` is a reduction of `Y` by Stacks 0GB7 and is affine by
  the affine case of Stacks 0AIN.
* `AlgebraicGeometry.FormalSpace.tfae_isQuasiCompactSpace_of_isReduction`: the equivalence of
  the three conditions, on the one hypothesis `hCoproductEtale` for the implication (2) ⇒ (3).

## References

* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0GB7](https://stacks.math.columbia.edu/tag/0GB7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The universe-lifted Yoneda image of a morphism of the big fppf site of `S` is surjective on
points if and only if the underlying morphism of schemes is surjective. -/
private theorem isSurjectiveULift_uliftYoneda_map_iff {U V : BigFppfOver B S hS} (m : U ⟶ V) :
    Space.IsSurjectiveULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).map m) ↔
      AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map m) :=
  (Space.isSurjectiveULift_whiskerRight_iff.{u + 1} B S hS (yoneda.map m)).trans
    ((Space.surjective_yonedaMap_iff_surjective_pointsMap B S hS m).symm.trans
      (Space.presheaf_yoneda_map_iff B S hS
        (P := @AlgebraicGeometry.Surjective.{u}) inferInstance m))

/-- A morphism of presheaves on the big fppf site of `S` with values in `Type (u + 1)` which is
surjective after every represented base change is surjective on points: a represented base
change is isomorphic to the chosen fibre product of presheaves, so each fibre product of the
morphism with a scheme-valued point of its target is surjective on points, and a morphism
representable by algebraic spaces with that property is surjective on points. -/
private theorem isSurjectiveULift_of_relative_surjective
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) a) :
    Space.IsSurjectiveULift.{u + 1} B S hS a := by
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a := fun A ξ ↦
    Space.isAlgebraicSpaceULift_of_iso B S hS (hsurj.rep.isPullback ξ).flip.isoPullback
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (hsurj.rep.pullback ξ))
  refine (hasPropertyULift_isSurjectiveULift_iff a hrep).mp ?_
  intro A ξ
  have hmap : Space.IsSurjectiveULift.{u + 1} B S hS
      ((uliftYoneda.{u + 1}).map (hsurj.rep.snd ξ)) :=
    (isSurjectiveULift_uliftYoneda_map_iff B S hS _).mpr (hsurj.property_snd ξ)
  have hfac : (hsurj.rep.isPullback ξ).flip.isoPullback.hom ≫ pullback.fst ξ a
      = (uliftYoneda.{u + 1}).map (hsurj.rep.snd ξ) :=
    (hsurj.rep.isPullback ξ).flip.isoPullback_hom_fst
  change Space.IsSurjectiveULift.{u + 1} B S hS (pullback.fst ξ a)
  intro z
  obtain ⟨w, hw⟩ := hmap z
  refine ⟨Space.pointsMapULift.{u + 1} B S hS _
    (hsurj.rep.isPullback ξ).flip.isoPullback.hom w, ?_⟩
  rw [← Function.comp_apply (f := Space.pointsMapULift.{u + 1} B S hS _ (pullback.fst ξ a)),
    ← Space.pointsMapULift_comp, hfac, hw]

/-! ### The implication (3) ⇒ (1) -/

/-- A morphism of presheaves on the big fppf site of `S` with values in `Type (u + 1)` which is
representable by objects of the site and étale after every base change along an algebraic space
is étale after every *represented* base change: the represented base change is isomorphic to the
chosen fibre product of presheaves, and étaleness of a morphism out of a universe-lifted Yoneda
presheaf is étaleness of the underlying morphism of schemes. -/
private theorem relative_etale_of_hasPropertyULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (hsite : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable a)
    {hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a}
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) a hrep) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) a := by
  refine ⟨hsite, ?_⟩
  intro A b g p m hpb
  have hbase : (uliftYoneda.{u + 1}).map m
      = hpb.flip.isoPullback.hom ≫ pullback.fst g a :=
    (hpb.flip.isoPullback_hom_fst).symm
  change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map m)
  rw [← Space.isEtaleULift_uliftYoneda_map_iff.{u + 1, u} B S hS m, hbase]
  exact isEtaleULift_comp B S hS
    (isEtaleULift_of_isIso B S hS hpb.flip.isoPullback.hom) (het A g)

/-- A morphism of presheaves on the big fppf site of `S` with values in `Type (u + 1)` which is
representable by objects of the site and surjective on points is surjective after every
represented base change: a point of the test object and a point of the source above its image
lift to a point of the base change, and surjectivity on points of a morphism of the site is
surjectivity of the underlying morphism of schemes. -/
private theorem relative_surjective_of_isSurjectiveULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (hsite : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable a)
    (hsurj : Space.IsSurjectiveULift.{u + 1} B S hS a) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) a := by
  refine ⟨hsite, ?_⟩
  intro A b g p m hpb
  refine (isSurjectiveULift_uliftYoneda_map_iff B S hS m).mp ?_
  intro z
  obtain ⟨x, hx⟩ := hsurj (Space.pointsMapULift.{u + 1} B S hS _ g z)
  obtain ⟨v, hv, -⟩ := Space.exists_point_of_isPullbackULift B S hS hpb.flip z x hx.symm
  exact ⟨v, hv⟩

/-- A presheaf on the big fppf site of `S` with values in `Type (u + 1)` which receives a
morphism from a presheaf isomorphic to the universe-lifted Yoneda presheaf of an object of the
site with compact underlying scheme, representable by algebraic spaces, étale and surjective on
points, is a quasi-compact algebraic space over `S`.

Such a morphism is representable by *objects* of the site, by Stacks 0AHV in the form
`AlgebraicGeometry.Space.relativelyRepresentableULift_of_isEtale_of_schemeSource`; the
representing objects are étale over the test object because the base change is, and surjective
over it because a point of the test object and a point of the source over its image lift to a
point of the base change. -/
private theorem isQuasiCompactSpaceULift_of_isEtale_of_isSurjective_of_schemeSource
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : F ⟶ G)
    (T : BigFppfOver B S hS) (e : (uliftYoneda.{u + 1}).obj T ≅ F)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) a hrep)
    (hsurj : Space.IsSurjectiveULift.{u + 1} B S hS a) :
    Space.IsQuasiCompactSpaceULift.{u + 1} B S hS G := by
  have hsite := Space.relativelyRepresentableULift_of_isEtale_of_schemeSource B S hS a T e
    hrep het
  refine ⟨T, e.hom ≫ a, hT, ?_, ?_⟩
  · exact MorphismProperty.RespectsIso.precomp _ e.hom a
      (relative_surjective_of_isSurjectiveULift B S hS hsite hsurj)
  · exact (Space.isEtaleULift_iff_relative_etale.{u + 1} B S hS (e.hom ≫ a)).mpr
      (MorphismProperty.RespectsIso.precomp _ e.hom a
        (relative_etale_of_hasPropertyULift B S hS hsite het))

/-- **Stacks 0AJ9, the implication (3) ⇒ (1).** Let `X` be a quasi-compact formal algebraic
space over `S` and let `i : Xred ⟶ X` be a reduction of `X`. Then `Xred` is a quasi-compact
algebraic space.

Let `c : Y ⟶ X` be the morphism of condition (3), with `Y` an affine formal algebraic space.
The fibre product `P = Y ×_X Xred` is a reduction of `Y` by **Stacks 0GB7**, an étale morphism
being smooth, so `P` is the sheaf of an affine object `T` of the site by the affine case of
Stacks 0AIN. The second projection `P ⟶ Xred` is a base change of `c`, hence representable by
algebraic spaces and étale, and it is surjective on points because `c` is; so `T ⟶ Xred` is a
quasi-compact surjective étale chart of `Xred`. -/
@[stacks 0AJ9 "the implication (3) ⇒ (1), for every reduction i : Xred ⟶ X of X, a reduction \
existing by Stacks 0AIN (exists_isReduction_of_isFormalAlgebraicSpace); nothing is assumed \
beyond the source's hypotheses"]
theorem IsQuasiCompactSpace.isQuasiCompactSpaceULift_of_isReduction
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X} (hi : IsReduction B S hS X Xred i)
    (h : IsQuasiCompactSpace B S hS X) :
    Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj := by
  have hX : IsFormalAlgebraicSpace B S hS X := h.isFormalAlgebraicSpace B S hS
  obtain ⟨-, Y, c, haffine, hc, hsurjective⟩ := h
  have hY : IsFormalAlgebraicSpace B S hS Y :=
    isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS haffine
  -- Stacks 0GB7: the fibre product `Y ×_X Xred` is a reduction of `Y`
  have hsmooth : Space.HasPropertyULift.{u + 1} B S hS
      (Space.smoothPropertyULift.{u + 1} B S hS) c.hom hc.1 := fun U ξ ↦
    holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
      (fun k hk ↦ by have : Etale k := hk; infer_instance) _ (hc.2 U ξ)
  have sq : IsPullback (pullback.fst c i) (pullback.snd c i) c i :=
    IsPullback.of_hasPullback c i
  have hP : IsReduction B S hS Y (pullback c i) (pullback.fst c i) :=
    isReduction_pullback_reduction_of_smooth B S hS hY hX hc.1 hsmooth hi sq
  -- the affine case of Stacks 0AIN presents that reduction by an affine object of the site
  obtain ⟨Y₀, i₀, T, hTaff, ⟨e₀⟩, h₀⟩ :=
    exists_isReduction_isAffine_of_isAffineFormalAlgebraicSpace B S hS Y haffine
  obtain ⟨k, hk, -⟩ := h₀.universal (pullback c i) hP.algebraic hP.reduced (pullback.fst c i)
  have _ : IsIso k := IsReduction.isIso_of_comp_eq B S hS hP h₀ hk
  have e : (uliftYoneda.{u + 1}).obj T ≅ (pullback c i).obj :=
    e₀ ≪≫ ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso
      (asIso k)).symm
  -- the second projection is representable by algebraic spaces, étale and surjective
  have hsnd : IsRepresentableEtale B S hS (pullback.snd c i) :=
    isRepresentableEtale_of_isPullback B S hS sq hc
  have hsndSurj : Space.IsSurjectiveULift.{u + 1} B S hS (pullback.snd c i).hom :=
    IsSurjective.of_isPullback B S hS sq.flip
      (isSurjective_of_isLocallySurjective B S hS hsurjective)
  have _ := hTaff
  exact isQuasiCompactSpaceULift_of_isEtale_of_isSurjective_of_schemeSource B S hS
    (pullback.snd c i).hom T e (Scheme.compactSpace_of_isAffine _) hsnd.1 hsnd.2 hsndSurj

/-! ### The implication (1) ⇒ (2) -/

/-- The point of the representing scheme underlying a point of the universe-lifted Yoneda
presheaf of an object of the big fppf site of `S`: the composite of the identification of the
two notions of point in the two value universes with the identification of the points of a
represented presheaf with the points of the representing scheme. -/
private noncomputable def pointULiftToScheme (U : BigFppfOver B S hS)
    (p : Space.pointsULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U)) :
    (BigFppfOver.toScheme B S hS).obj U :=
  Space.pointsToScheme B S hS U ((Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U)).symm p)

/-- Every point of the scheme representing an object of the big fppf site of `S` comes from a
point of the universe-lifted Yoneda presheaf of that object. -/
private theorem surjective_pointULiftToScheme (U : BigFppfOver B S hS) :
    Function.Surjective (pointULiftToScheme B S hS U) := by
  intro t
  obtain ⟨x, hx⟩ := Space.surjective_pointsToScheme B S hS U t
  exact ⟨Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U) x, by
    simpa only [pointULiftToScheme, Equiv.symm_apply_apply] using hx⟩

/-- Two points of the universe-lifted Yoneda presheaf of an object of the big fppf site of `S`
with the same underlying point of the representing scheme are equal. -/
private theorem injective_pointULiftToScheme (U : BigFppfOver B S hS) :
    Function.Injective (pointULiftToScheme B S hS U) := fun _ _ h ↦
  (Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U)).symm.injective
    (Space.injective_pointsToScheme B S hS U h)

/-- Applying a morphism of the big fppf site of `S` to a point of a universe-lifted Yoneda
presheaf moves the underlying point of the representing scheme along the underlying morphism of
schemes. -/
private theorem pointULiftToScheme_pointsMapULift {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (p : Space.pointsULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U)) :
    pointULiftToScheme B S hS V
        (Space.pointsMapULift.{u + 1} B S hS _ ((uliftYoneda.{u + 1}).map g) p) =
      (BigFppfOver.toScheme B S hS).map g (pointULiftToScheme B S hS U p) := by
  obtain ⟨x, rfl⟩ := (Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U)).surjective p
  have hnat : Space.pointsMapULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U)
        ((uliftYoneda.{u + 1}).map g)
        (Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U) x) =
      Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj V)
        (Space.pointsMap B S hS (yoneda.obj U) (yoneda.map g) x) :=
    congrFun (Space.pointsMapULift_whiskerRight_pointsULiftEquiv.{u + 1} B S hS
      (yoneda.map g)) x
  simp only [pointULiftToScheme, hnat, Equiv.symm_apply_apply]
  exact Space.pointsToScheme_pointsMap B S hS g x

/-- **A family of charts jointly surjective on points is jointly surjective as a family of
sheaves.** Let `{Xᵢ ⟶ X}` be a family of morphisms of fppf sheaves over `S` whose sources are
affine formal algebraic spaces and which are representable by algebraic spaces and étale, as in
Definition **Stacks 0AIM** but with joint surjectivity replaced by joint surjectivity on the
points of Stacks 03BU. Then the induced morphism from the coproduct is a surjection of sheaves,
so the family is a covering as in Definition 0AIM.

Each member is representable by objects of the site by **Stacks 0AIG**, so for a section `y` of
`X` over an object `T` of the site the base changes `Vᵢ = Xᵢ ×_X T` are objects of the site and
the morphisms `Vᵢ ⟶ T` are étale. Joint surjectivity on points makes them jointly surjective on
the points of `T`: a point of `T` is a point of the universe-lifted Yoneda presheaf of `T`, its
image in `X` lifts to some `Xᵢ`, and the two lift to a point of `Vᵢ`. An étale, jointly
surjective family of morphisms of the site generates a covering sieve, and `y` lifts to `Xᵢ`
over `Vᵢ`, so the image sieve of the morphism from the coproduct at `y` is a covering sieve. -/
theorem isLocallySurjective_sigmaDesc_of_jointlySurjective_points {I : Type (u + 1)}
    {Xi : I → FppfSheaf B S hS} {X : FppfSheaf B S hS} (f : ∀ i, Xi i ⟶ X)
    (haffine : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i))
    (hf : ∀ i, IsRepresentableEtale B S hS (f i))
    (hpoints : ∀ p : Space.pointsULift.{u + 1} B S hS X.obj, ∃ (i : I)
      (z : Space.pointsULift.{u + 1} B S hS (Xi i).obj),
      Space.pointsMapULift.{u + 1} B S hS (Xi i).obj (f i).hom z = p) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc f) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  -- Stacks 0AIG: each member is representable by objects of the site
  have hrep : ∀ i, (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable
      (f i).hom := fun i ↦
    relativelyRepresentable_of_isEtale_of_isAffineFormal B S hS (f i) (haffine i)
      (hf i).1 (hf i).2
  have hetRel : ∀ i, (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) (f i).hom := fun i ↦
    relative_etale_of_hasPropertyULift B S hS (hrep i) (hf i).2
  constructor
  intro T y
  set ξ : (uliftYoneda.{u + 1}).obj T ⟶ X.obj := uliftYonedaEquiv.{u + 1}.symm y with hξ
  set V : I → BigFppfOver B S hS := fun i ↦ (hrep i).pullback ξ
  set q : ∀ i, V i ⟶ T := fun i ↦ (hrep i).snd ξ
  -- each base change is étale, hence flat and locally of finite presentation
  have hqEtale : ∀ i, AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (q i)) :=
    fun i ↦ (hetRel i).property ξ ((hrep i).fst ξ) (q i) ((hrep i).isPullback ξ)
  -- the base changes are jointly surjective on the points of `T`
  have hqSurj : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q i)) := by
    intro t
    obtain ⟨pt, hpt⟩ := surjective_pointULiftToScheme B S hS T t
    obtain ⟨i, z, hz⟩ := hpoints (Space.pointsMapULift.{u + 1} B S hS _ ξ pt)
    obtain ⟨v, -, hv⟩ :=
      Space.exists_point_of_isPullbackULift B S hS ((hrep i).isPullback ξ) z pt hz
    refine ⟨i, pointULiftToScheme B S hS (V i) v, ?_⟩
    rw [← pointULiftToScheme_pointsMapULift B S hS (q i) v, hv, hpt]
  -- an étale, jointly surjective family of morphisms of the site generates a covering sieve
  have hfam := mem_topology_of_family B S hS (U := T) (fun i ↦ (V i).left)
    (fun i ↦ (q i).left)
    (fun i ↦ by
      have := hqEtale i
      change AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map (q i))
      infer_instance)
    (fun i ↦ by
      have := hqEtale i
      change AlgebraicGeometry.LocallyOfFinitePresentation
        ((BigFppfOver.toScheme B S hS).map (q i))
      infer_instance)
    hqSurj
  have hle : Sieve.ofArrows (fun i ↦ (Over.mk ((q i).left ≫ T.hom) : BigFppfOver B S hS))
      (fun i ↦ (Over.homMk ((q i).left) : Over.mk ((q i).left ≫ T.hom) ⟶ T)) ≤
      Sieve.ofArrows V q := by
    refine (Sieve.generate_le_iff _ _).mpr ?_
    rintro W k ⟨i⟩
    refine ⟨V i, Over.homMk (𝟙 (V i).left) (by simp), q i, ⟨i⟩, ?_⟩
    ext
    simp
  have hcover : Sieve.ofArrows V q ∈ BigFppfOver.topology B S hS T :=
    (BigFppfOver.topology B S hS).superset_covering hle hfam
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hcover
  refine (Sieve.generate_le_iff _ _).mpr ?_
  rintro W k ⟨i⟩
  refine ⟨uliftYonedaEquiv.{u + 1} ((hrep i).fst ξ ≫ (Sigma.ι Xi i).hom), ?_⟩
  have hι : (Sigma.ι Xi i).hom ≫ (Sigma.desc f).hom = (f i).hom := by
    have h : (Sigma.ι Xi i ≫ Sigma.desc f).hom = (f i).hom := by rw [Sigma.ι_desc]
    exact h
  calc (Sigma.desc f).hom.app _ (uliftYonedaEquiv.{u + 1}
          ((hrep i).fst ξ ≫ (Sigma.ι Xi i).hom))
      = uliftYonedaEquiv.{u + 1}
          (((hrep i).fst ξ ≫ (Sigma.ι Xi i).hom) ≫ (Sigma.desc f).hom) :=
        (uliftYonedaEquiv_comp.{u + 1} _ _).symm
    _ = uliftYonedaEquiv.{u + 1} ((hrep i).fst ξ ≫ (f i).hom) := by
        rw [Category.assoc, hι]
    _ = uliftYonedaEquiv.{u + 1} ((uliftYoneda.{u + 1}).map (q i) ≫ ξ) := by
        rw [((hrep i).isPullback ξ).w]
    _ = X.obj.map (q i).op y := by
        have hnat := uliftYonedaEquiv_naturality.{u + 1} ξ (q i).op
        simp only [Quiver.Hom.unop_op] at hnat
        rw [← hnat, hξ, Equiv.apply_symm_apply]

/-- **A finite subfamily of a given covering of a formal algebraic space with quasi-compact
reduction.** Let `X` be an fppf sheaf over `S`, let `i : Xred ⟶ X` be a reduction of `X` which
is a quasi-compact algebraic space and let `{Wⱼ ⟶ X}` be a covering as in Definition **0AIM**.
Then finitely many members of that covering already cover `X`.

Let `φ : U ⟶ Xred` be a quasi-compact surjective étale chart of `Xred`. The base changes of the
covering along the composite `U ⟶ Xred ⟶ X` are objects of the site by **Stacks 0AIG**, étale
over `U`, and jointly surjective on its points, so finitely many of them already cover the
compact space `U`,
`AlgebraicGeometry.FormalSpace.exists_finite_subfamily_pullback_cover_of_compactSpace`. That
finite subfamily is still jointly surjective on the points of `X`: a point of `X` is a point of
`Xred`, the inclusion of a reduction being bijective on points, hence comes from a point of `U`,
which is met by one of the finitely many base changes. A family of affine formal charts jointly
surjective on points is a covering as in Definition 0AIM,
`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_jointlySurjective_points`.

This is the sharp form of the implication (1) ⇒ (2) of **Stacks 0AJ9**: the tag asks only that
*some* finite covering exist, which is
`AlgebraicGeometry.FormalSpace.hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_reduction`
below, whereas the proof of **Stacks 0ANG** needs the finite family to be a subfamily of the
covering it started from, because the data attached to that covering — the factorizations of its
members through charts of the target — must survive the shrinking. -/
theorem exists_finite_subcover_of_isQuasiCompactSpaceULift_reduction
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X} {I : Type (u + 1)} {W : I → FppfSheaf B S hS}
    (w : ∀ j, W j ⟶ X) (hWaffine : ∀ j, IsAffineFormalAlgebraicSpace B S hS (W j))
    (hWetale : ∀ j, IsRepresentableEtale B S hS (w j))
    (hWcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc w))
    (hi : IsReduction B S hS X Xred i)
    (hqc : Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj) :
    ∃ (σ : Type (u + 1)) (_ : Finite σ) (κ : σ → I),
      letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fun s ↦ w (κ s)) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨U, φ, hUcompact, hφSurj, -⟩ := hqc
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := hUcompact
  obtain ⟨σ, κ, V, q, ζ, hfinite, hsq, -, hcover⟩ :=
    exists_finite_subfamily_pullback_cover_of_compactSpace B S hS w hWaffine hWetale hWcover
      (φ ≫ i.hom)
  refine ⟨σ, hfinite, κ, isLocallySurjective_sigmaDesc_of_jointlySurjective_points B S hS
    (fun s ↦ w (κ s)) (fun s ↦ hWaffine (κ s)) (fun s ↦ hWetale (κ s)) ?_⟩
  intro p
  obtain ⟨pred, hpred⟩ := hi.bijective_pointsMapULift.2 p
  obtain ⟨pu, hpu⟩ := isSurjectiveULift_of_relative_surjective B S hS hφSurj pred
  obtain ⟨k, x, hx⟩ := hcover (pointULiftToScheme B S hS U pu)
  obtain ⟨pv, hpv⟩ := surjective_pointULiftToScheme B S hS (V k) x
  have hqpv : Space.pointsMapULift.{u + 1} B S hS _
      ((uliftYoneda.{u + 1}).map (q k)) pv = pu := by
    refine injective_pointULiftToScheme B S hS U ?_
    rw [pointULiftToScheme_pointsMapULift B S hS (q k) pv, hpv, hx]
  refine ⟨k, Space.pointsMapULift.{u + 1} B S hS _ (ζ k) pv, ?_⟩
  calc Space.pointsMapULift.{u + 1} B S hS (W (κ k)).obj (w (κ k)).hom
        (Space.pointsMapULift.{u + 1} B S hS _ (ζ k) pv)
      = Space.pointsMapULift.{u + 1} B S hS _ (ζ k ≫ (w (κ k)).hom) pv := by
        rw [Space.pointsMapULift_comp]
        rfl
    _ = Space.pointsMapULift.{u + 1} B S hS _
          ((uliftYoneda.{u + 1}).map (q k) ≫ (φ ≫ i.hom)) pv := by rw [(hsq k).w]
    _ = Space.pointsMapULift.{u + 1} B S hS _ (φ ≫ i.hom)
          (Space.pointsMapULift.{u + 1} B S hS _ ((uliftYoneda.{u + 1}).map (q k)) pv) := by
        rw [Space.pointsMapULift_comp]
        rfl
    _ = Space.pointsMapULift.{u + 1} B S hS _ (φ ≫ i.hom) pu := by rw [hqpv]
    _ = Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom
          (Space.pointsMapULift.{u + 1} B S hS _ φ pu) := by
        rw [Space.pointsMapULift_comp]
        rfl
    _ = p := by rw [hpu, hpred]

/-- **A finite subfamily of a covering of an affine formal algebraic space.** A covering
`{Wⱼ ⟶ U₀}` as in Definition **0AIM** of an affine formal algebraic space `U₀` over `S` has a
finite subfamily which is again such a covering.

An affine formal algebraic space has a reduction which is the sheaf of an affine object of the
site, the affine case of **Stacks 0AIN**, and any reduction of it is then a quasi-compact
algebraic space, `AlgebraicGeometry.FormalSpace.affineReductionsQuasiCompact`; so this is the
sharp form of the implication (1) ⇒ (2) of **Stacks 0AJ9** specialised to an affine formal
algebraic space. It is the step the proof of **Stacks 0ANG** performs on the chart of its
condition (1), where the subfamily must be a subfamily of the covering supplied, since the
factorizations of that covering's members through charts of the target have to survive the
shrinking.

Note that the restriction to coverings as in Definition 0AIM is essential and not a
convenience: an affine formal algebraic space is *not* quasi-compact as an object of the topos,
since the stages of `Spf k⟦t⟧` are jointly locally surjective onto it with no finite subfamily,
and they escape the statement only because a thickening is not representable étale. -/
theorem exists_finite_subcover_of_isAffineFormalAlgebraicSpace {I : Type (u + 1)}
    (U₀ : FppfSheaf B S hS) (W : I → FppfSheaf B S hS) (w : ∀ j, W j ⟶ U₀)
    (hU₀ : IsAffineFormalAlgebraicSpace B S hS U₀) (hW : IsAffineEtaleCover B S hS W w) :
    ∃ (σ : Type (u + 1)) (_ : Finite σ) (κ : σ → I),
      IsAffineEtaleCover B S hS (fun s ↦ W (κ s)) (fun s ↦ w (κ s)) := by
  obtain ⟨Ured, iU, -, -, -, hiU⟩ :=
    exists_isReduction_isAffine_of_isAffineFormalAlgebraicSpace B S hS U₀ hU₀
  obtain ⟨σ, hfinite, κ, hsub⟩ := exists_finite_subcover_of_isQuasiCompactSpaceULift_reduction
    B S hS w hW.1 hW.2.1 hW.2.2 hiU
    (affineReductionsQuasiCompact B S hS U₀ Ured iU hU₀ hiU)
  exact ⟨σ, hfinite, κ, fun s ↦ hW.1 (κ s), fun s ↦ hW.2.1 (κ s), hsub⟩

/-! ### The equivalence of the three conditions -/

/-- **Stacks 0AJ9.** Let `X` be a formal algebraic space over `S` and let `i : Xred ⟶ X` be a
reduction of `X`. The following are equivalent:

1. `Xred` is a quasi-compact algebraic space,
2. `X` admits an atlas as in Definition 0AIM indexed by a finite type,
3. `X` receives a morphism from an affine formal algebraic space which is representable by
   algebraic spaces, étale and a surjection of sheaves. -/
theorem tfae_isQuasiCompactSpace_of_isReduction
    (hCoproductEtale : CoproductsRepresentableEtale B S hS)
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (hX : IsFormalAlgebraicSpace B S hS X) (hi : IsReduction B S hS X Xred i) :
    [Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj,
      HasFiniteFormalAtlas B S hS X,
      IsQuasiCompactSpace B S hS X].TFAE := by
  tfae_have 1 → 2 := hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_reduction B S hS hX hi
  tfae_have 2 → 3 := HasFiniteFormalAtlas.isQuasiCompactSpace B S hS hCoproductEtale
  tfae_have 3 → 1 := IsQuasiCompactSpace.isQuasiCompactSpaceULift_of_isReduction B S hS hi
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
