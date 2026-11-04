module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionFunctorCovering
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionFunctorLimits
public import StacksFrontier.CategoryTheory.Sites.Continuous

/-!
# The morphism of ringed topoi from a category fibred in groupoids to its algebraic space

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`F`, and let `u : F_étale ⥤ 𝒳` be the functor attached to an equivalence over the site between
`𝒳` and the category of elements of the sheaf of points of `F`. Restriction along `u` is the
direct image of a morphism of topoi `π_F : Sh(𝒳_étale) ⟶ Sh(F_étale)` whose inverse image is the
left adjoint `g_!` of restriction, and the restricted structure sheaf of `𝒳` is the structure
sheaf of `F`, so `π_F` is a morphism of ringed topoi.

The one substantive point is that `g_!` is left exact. On finite *connected* shapes this holds
for any continuous functor whose source has fibre products and equalizers which it preserves,
and the terminal object is the remaining case: `u_p` of the final presheaf on `F_étale` has
subsingleton sections, because each comma category `StructuredArrow X u` is cofiltered or empty,
and it is locally nonempty, because every object of `𝒳` is covered by objects admitting a
morphism into the image of `u`. A locally surjective morphism out of a subterminal presheaf
sheafifies to an isomorphism, so `g_!` carries the final sheaf on `F_étale` to the final sheaf
on `𝒳_étale`.

With `π_F` available, equation 075K is complete: the restriction `ℱ|_{F_étale}` of a sheaf of
sets, defined as restriction along `u`, is both the inverse image `i_F^{-1}ℱ` and the direct
image `π_{F,*}ℱ`, and its sections are `ℱ(u(U))`.

## Main definitions

* `AlgebraicGeometry.Space.projectionRingedToposHom`: the morphism of ringed topoi
  `π_F : (Sh(𝒳_étale), 𝒪_𝒳) ⟶ (Sh(F_étale), 𝒪_F)`.
* `AlgebraicGeometry.Space.projectionPushforward`: its direct image `π_{F,*}` on sheaves of
  sets.

## Main results

* `AlgebraicGeometry.Space.essentiallySmall_of_equivalenceOver`: a category fibred in groupoids
  representable by an algebraic space over `S` is essentially small at the universe of the
  schemes of the site.
* `AlgebraicGeometry.Space.preservesFiniteLimits_restrictionSheafPullback`: the left adjoint
  `g_!` of restriction along `F_étale ⥤ 𝒳` is left exact.
* `AlgebraicGeometry.Space.projectionRingedToposHom_pushforward`: the direct image of `π_F` is
  restriction along the functor `F_étale ⥤ 𝒳`.
* `AlgebraicGeometry.Space.restrictionSheafFunctor_eq_projectionPushforward`,
  `AlgebraicGeometry.Space.restrictionSheafFunctor_eq_restrictionToposHom_inverseImage` and
  `AlgebraicGeometry.Space.projectionPushforward_obj_obj`: **equation 075K**,
  `ℱ|_{F_étale} = i_F^{-1}ℱ = π_{F,*}ℱ`, together with the computation
  `π_{F,*}ℱ(U) = ℱ(u(U))` it abbreviates.

## Implementation notes

The site `𝒳` of Stacks 06TP has its objects in a universe unrelated to the universe `u` of the
schemes, while its structure sheaf takes sections in `Type u`, so the sheafification conditions
on the inherited étale site are not instances by Mathlib's size-matched route. They are not
assumed either: the chosen equivalence presents `𝒳` as the scheme charts of `F`, hence as a
category essentially small at `u`, and sheafification of `Type u`-valued presheaves on an
essentially small site exists and is left exact. The same essential smallness supplies the
colimits computing `u_p` and hence the existence of `g_!`.

`CategoryTheory.Functor.preservesLimitsOfShape_sheafPullback` asks the comma categories
`CostructuredArrow u.op Y` to be `u`-small, which for a site of schemes they are not — the type
of objects of the small étale site of `F` is only *essentially* `u`-small. The private
`preservesLimitsOfShape_sheafPullback_of_essentiallySmall` below weakens that hypothesis by
replacing `u` with its restriction to a small model of the source site: the two restriction
functors on sheaves differ by an equivalence of sheaf categories, so their left adjoints differ
by that equivalence as well.

## References

* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Equation 075K](https://stacks.math.columbia.edu/tag/075K)
* [Stacks Project, Tag 00XS](https://stacks.math.columbia.edu/tag/00XS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

section SheafPullback

universe w t v₁ v₂ u₁ u₂

/-- Stacks 00XS over an essentially small source site: if `C` has fibre products and equalizers
which the continuous functor `u : C ⥤ D` preserves, then `g_!` preserves limits of every finite
connected shape. Essential smallness of `C` replaces smallness of the comma categories
`CostructuredArrow u.op Y`, by comparing `u` with its restriction to a small model of `C`. -/
private theorem preservesLimitsOfShape_sheafPullback_of_essentiallySmall
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u] [PreservesLimitsOfShape WalkingParallelPair u]
    [HasSheafify K (Type w)] [EssentiallySmall.{w} C] [LocallySmall.{w} D]
    [(u.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
    (I : Type t) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (u.sheafPullback (Type w) J K) := by
  set ε := equivSmallModel.{w} C
  set J₀ := ε.inverse.inducedTopology J
  let : (ε.inverse ⋙ u).IsContinuous J₀ K := Functor.isContinuous_comp ε.inverse u J₀ J K
  let : HasPullbacks (SmallModel.{w} C) :=
    Adjunction.hasLimitsOfShape_of_equivalence ε.inverse
  let : HasEqualizers (SmallModel.{w} C) :=
    Adjunction.hasLimitsOfShape_of_equivalence ε.inverse
  have h0 : PreservesLimitsOfShape I ((ε.inverse ⋙ u).sheafPullback (Type w) J₀ K) :=
    Functor.preservesLimitsOfShape_sheafPullback (ε.inverse ⋙ u) J₀ K I
  let Ψ : Sheaf J₀ (Type w) ≌ Sheaf J (Type w) := (ε.sheafCongr J J₀ (Type w)).symm
  let adj : (Ψ.functor ⋙ u.sheafPullback (Type w) J K) ⊣
      (u.sheafPushforwardContinuous (Type w) J K ⋙ Ψ.inverse) :=
    Ψ.toAdjunction.comp (u.sheafAdjunctionContinuous (Type w) J K)
  have h1 : PreservesLimitsOfShape I (Ψ.functor ⋙ u.sheafPullback (Type w) J K) :=
    preservesLimitsOfShape_of_natIso
      (Adjunction.leftAdjointUniq
        ((ε.inverse ⋙ u).sheafAdjunctionContinuous (Type w) J₀ K) adj)
  have h2 : PreservesLimitsOfShape I
      ((Ψ.inverse ⋙ Ψ.functor) ⋙ u.sheafPullback (Type w) J K) :=
    comp_preservesLimitsOfShape Ψ.inverse (Ψ.functor ⋙ u.sheafPullback (Type w) J K)
  exact preservesLimitsOfShape_of_natIso
    (Functor.isoWhiskerRight Ψ.counitIso (u.sheafPullback (Type w) J K))

/-- The point of a colimit of sets with subsingleton values over an index category any two of
whose objects admit morphisms to a common third is a subsingleton: the cocone is jointly
surjective, and two of its values are identified over a common target. -/
private theorem subsingleton_coconePt {I : Type u₁} [Category.{v₁} I] {G : I ⥤ Type w}
    {c : Cocone G} (hc : IsColimit c) (hsub : ∀ i, Subsingleton (G.obj i))
    (hjoin : ∀ i j : I, ∃ (k : I) (_ : i ⟶ k), Nonempty (j ⟶ k)) :
    Subsingleton c.pt := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨i, a, rfl⟩ := Types.jointly_surjective_of_isColimit hc x
  obtain ⟨j, b, rfl⟩ := Types.jointly_surjective_of_isColimit hc y
  obtain ⟨k, f, ⟨g⟩⟩ := hjoin i j
  have e₁ := ConcreteCategory.congr_hom (c.w f) a
  have e₂ := ConcreteCategory.congr_hom (c.w g) b
  rw [ConcreteCategory.comp_apply] at e₁ e₂
  have := hsub k
  rw [← e₁, ← e₂, Subsingleton.elim (G.map f a) (G.map g b)]

/-- The remaining, non-connected case of Stacks 00XS: if every comma category
`StructuredArrow X u` of a continuous functor `u : C ⥤ D` is cofiltered or empty, and the
morphisms into `X` whose source admits a morphism to the image of `u` form a covering sieve,
then `g_!` carries the final sheaf on `C` to the final sheaf on `D`.

The presheaf `u_p` of the final presheaf has subsingleton sections, since its sections are a
colimit of singletons over a category with at most one connected component, and the morphism
from it to the final presheaf is locally surjective, since its image sieve at an object contains
the covering sieve above. A locally surjective morphism out of a subterminal presheaf of sets
sheafifies to an isomorphism. -/
private theorem preservesTerminal_sheafPullback
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [HasSheafify K (Type w)]
    [K.WEqualsLocallyBijective (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseLeftKanExtension P]
    [∀ X : D, IsCofilteredOrEmpty (StructuredArrow X u)]
    (hmem : ∀ X : D, u.structuredArrowSieve X ∈ K X) :
    PreservesLimitsOfShape (Discrete.{0} PEmpty.{1}) (u.sheafPullback (Type w) J K) := by
  let P : Cᵒᵖ ⥤ Type w := (Functor.const Cᵒᵖ).obj PUnit
  have hP : IsTerminal P := Functor.isTerminalConst _ Types.isTerminalPUnit
  let R : Dᵒᵖ ⥤ Type w := (Functor.const Dᵒᵖ).obj PUnit
  have hR : IsTerminal R := Functor.isTerminalConst _ Types.isTerminalPUnit
  have hcol : ∀ X : Dᵒᵖ, IsColimit
      ((Functor.LeftExtension.mk (u.op.lan.obj P) (u.op.lanUnit.app P)).coconeAt X) :=
    Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ (u.op.lanUnit.app P)
  have hjoin : ∀ (X : Dᵒᵖ) (Z W : CostructuredArrow u.op X),
      ∃ (T : CostructuredArrow u.op X) (_ : Z ⟶ T), Nonempty (W ⟶ T) := by
    intro X Z W
    let e := structuredArrowOpEquivalence u X.unop
    obtain ⟨T, α, β, -⟩ := IsFilteredOrEmpty.cocone_objs (e.inverse.obj Z) (e.inverse.obj W)
    exact ⟨e.functor.obj T, (e.counitIso.app Z).inv ≫ e.functor.map α,
      ⟨(e.counitIso.app W).inv ≫ e.functor.map β⟩⟩
  have hsub : ∀ X : Dᵒᵖ, Subsingleton ((u.op.lan.obj P).obj X) := fun X =>
    subsingleton_coconePt (hcol X)
      (fun _ => inferInstanceAs (Subsingleton PUnit.{w + 1})) (hjoin X)
  have hτ : Presheaf.IsLocallySurjective K (hR.from (u.op.lan.obj P)) := by
    refine ⟨fun {X} s => K.superset_covering ?_ (hmem X)⟩
    rintro Y g ⟨V⟩
    let Z : CostructuredArrow u.op (Opposite.op Y) :=
      (structuredArrowOpEquivalence u Y).functor.obj (Opposite.op V)
    exact ⟨(u.op.lan.obj P).map Z.hom ((u.op.lanUnit.app P).app Z.left PUnit.unit),
      Subsingleton.elim (α := PUnit.{w + 1}) _ _⟩
  have : IsIso ((presheafToSheaf K (Type w)).map (hR.from (u.op.lan.obj P))) :=
    Presheaf.isIso_presheafToSheaf_map_of_subsingleton K
      (hR.from (u.op.lan.obj P)) hsub hτ
  have i₁ : (sheafToPresheaf J (Type w)).obj (⊤_ (Sheaf J (Type w))) ≅ P :=
    (IsTerminal.isTerminalObj (sheafToPresheaf J (Type w)) _ terminalIsTerminal).uniqueUpToIso hP
  have i₂ : (presheafToSheaf K (Type w)).obj R ≅ ⊤_ (Sheaf K (Type w)) :=
    (IsTerminal.isTerminalObj (presheafToSheaf K (Type w)) R hR).uniqueUpToIso terminalIsTerminal
  have hiso : (Functor.sheafPullbackConstruction.sheafPullback u (Type w) J K).obj
      (⊤_ (Sheaf J (Type w))) ≅ ⊤_ (Sheaf K (Type w)) :=
    (u.op.lan ⋙ presheafToSheaf K (Type w)).mapIso i₁ ≪≫
      asIso ((presheafToSheaf K (Type w)).map (hR.from (u.op.lan.obj P))) ≪≫ i₂
  have : PreservesLimit (Functor.empty.{0} (Sheaf J (Type w)))
      (Functor.sheafPullbackConstruction.sheafPullback u (Type w) J K) :=
    preservesTerminal_of_iso _ hiso
  have : PreservesLimit (Functor.empty.{0} (Sheaf J (Type w)))
      (u.sheafPullback (Type w) J K) :=
    preservesLimit_of_natIso _
      (Functor.sheafPullbackConstruction.sheafPullbackIso u (Type w) J K).symm
  exact preservesLimitsOfShape_pempty_of_preservesTerminal _

end SheafPullback

namespace AlgebraicGeometry.Space

universe u v w

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **Stacks 073M.** The left adjoint `g_!` of restriction along the functor `F_étale ⥤ 𝒳` is
left exact. Fibre products and equalizers are inherited from the small étale site of `F`, which
the functor preserves, and the final sheaf is carried to the final sheaf because the comma
categories of the functor are cofiltered and locally nonempty. -/
theorem preservesFiniteLimits_restrictionSheafPullback (hp : p.IsFiberedInGroupoids)
    (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    letI := restrictionFunctor_isContinuous B S hS F p hp e
    letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
    letI : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) (Type u) :=
      hasSheafifyEssentiallySmallSite _ _
    letI : ∀ P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type u,
        (restrictionFunctor B S hS F p e).op.HasPointwiseLeftKanExtension P := fun _ Y =>
      letI := hasColimitsOfShape_of_essentiallySmall.{u}
        (CostructuredArrow (restrictionFunctor B S hS F p e).op Y) (Type u)
      inferInstance
    PreservesFiniteLimits ((restrictionFunctor B S hS F p e).sheafPullback (Type u)
      (SmallEtale.topology B S hS F)
      (BigFppfOver.associatedTopology B S hS p .etale)) := by
  let := restrictionFunctor_isContinuous B S hS F p hp e
  let : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
  let : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) (Type u) :=
    hasSheafifyEssentiallySmallSite _ _
  let : (BigFppfOver.associatedTopology B S hS p .etale).WEqualsLocallyBijective (Type u) :=
    .ofEssentiallySmall _
  let : ∀ P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type u,
      (restrictionFunctor B S hS F p e).op.HasPointwiseLeftKanExtension P := fun _ Y =>
    have := hasColimitsOfShape_of_essentiallySmall.{u}
      (CostructuredArrow (restrictionFunctor B S hS F p e).op Y) (Type u)
    inferInstance
  let : PreservesLimitsOfShape (Discrete.{0} PEmpty.{1})
      ((restrictionFunctor B S hS F p e).sheafPullback (Type u)
        (SmallEtale.topology B S hS F)
        (BigFppfOver.associatedTopology B S hS p .etale)) :=
    preservesTerminal_sheafPullback _ _ _
      (structuredArrowSieve_restrictionFunctor_mem B S hS F p hp hF e)
  let : PreservesLimitsOfShape WalkingCospan
      ((restrictionFunctor B S hS F p e).sheafPullback (Type u)
        (SmallEtale.topology B S hS F)
        (BigFppfOver.associatedTopology B S hS p .etale)) :=
    preservesLimitsOfShape_sheafPullback_of_essentiallySmall _ _ _ WalkingCospan
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

section RingedTopoi

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-- **Stacks 073M.** The morphism of ringed topoi
`π_F : (Sh(𝒳_étale), 𝒪_𝒳) ⟶ (Sh(F_étale), 𝒪_F)`: its direct image is restriction along the
functor `F_étale ⥤ 𝒳`, its inverse image is the left adjoint `g_!` of that restriction, which is
left exact, and its structure map is the identification of the restricted structure sheaf of
`𝒳` with the structure sheaf of `F`. -/
@[stacks 073M "the morphism of ringed topoi pi_F"]
noncomputable def projectionRingedToposHom (hp : p.IsFiberedInGroupoids)
    (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    RingedToposHom (FibredSite.associatedRingedTopos B S hS p hp .etale)
      (smallEtaleRingedTopos B S hS ⟨F, hF⟩) :=
  letI := restrictionFunctor_isContinuous B S hS F p hp e
  letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
  letI : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) (Type u) :=
    hasSheafifyEssentiallySmallSite _ _
  letI : ∀ P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type u,
      (restrictionFunctor B S hS F p e).op.HasPointwiseLeftKanExtension P := fun _ Y =>
    letI := hasColimitsOfShape_of_essentiallySmall.{u}
      (CostructuredArrow (restrictionFunctor B S hS F p e).op Y) (Type u)
    inferInstance
  { toToposHom :=
      { pushforward := (restrictionFunctor B S hS F p e).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
        inverseImage := (restrictionFunctor B S hS F p e).sheafPullback (Type u)
          (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
        adj := (restrictionFunctor B S hS F p e).sheafAdjunctionContinuous (Type u)
          (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
        preservesFiniteLimits :=
          preservesFiniteLimits_restrictionSheafPullback B S hS F p hp hF e }
    fSharp := eqToHom (inverseImage_structureSheaf_eq B S hS F p hp e hF).symm ≫
      (restrictionCommRingIso (SmallEtale.topology B S hS F)
        (BigFppfOver.associatedTopology B S hS p .etale)
        (restrictionFunctor B S hS F p e)
        (FibredSite.structureSheaf B S hS p hp .etale)).inv }

/-- **Stacks 073M, equation 075K.** The direct image of `π_F` is restriction along the functor
`F_étale ⥤ 𝒳`, that is, `π_{F,*}ℱ(U) = ℱ(u(U))`.

This is the right-hand identification `ℱ|_{F_étale} = π_{F, *}ℱ` of equation 075K: the
right-hand side here is the term that `AlgebraicGeometry.Space.restrictionSheafFunctor` names
`ℱ|_{F_étale}`. The left-hand identification `ℱ|_{F_étale} = i_F^{-1}ℱ` is
`AlgebraicGeometry.Space.restrictionToposHom_inverseImage`; together they give the chain. -/
@[simp, stacks 075K "the identification `ℱ|_{F_étale} = π_{F, *}ℱ`", stacks 073M "the direct \
image of pi_F is restriction along the functor"]
theorem projectionRingedToposHom_pushforward (hp : p.IsFiberedInGroupoids)
    (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    letI := restrictionFunctor_isContinuous B S hS F p hp e
    (projectionRingedToposHom B S hS F p hp hF e).toToposHom.pushforward =
      (restrictionFunctor B S hS F p e).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS F)
        (BigFppfOver.associatedTopology B S hS p .etale) :=
  rfl

/-- The direct image `π_{F,*} : Sh(𝒳_étale) ⥤ Sh(F_étale)` of the morphism of
ringed topoi `π_F`, read on sheaves of sets. -/
noncomputable abbrev projectionPushforward (hp : p.IsFiberedInGroupoids)
    (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u) ⥤
      Sheaf (SmallEtale.topology B S hS F) (Type u) :=
  (projectionRingedToposHom B S hS F p hp hF e).toToposHom.pushforward

/-- The leg of equation 075K `ℱ|_{F_étale} = π_{F,*}ℱ`. The restriction of a sheaf on the
inherited étale site of `𝒳` to the small étale site of the algebraic space `F` representing it
is the direct image along `π_F`. -/
theorem restrictionSheafFunctor_eq_projectionPushforward (hp : p.IsFiberedInGroupoids)
    (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    restrictionSheafFunctor B S hS F p hp e = projectionPushforward B S hS F p hp hF e :=
  rfl

/-- The leg of equation 075K `ℱ|_{F_étale} = i_F^{-1}ℱ`. The restriction is the inverse image
along the morphism of topoi `i_F`.

The size hypothesis that `AlgebraicGeometry.Space.restrictionToposHom` carries is not assumed:
it is supplied by `AlgebraicGeometry.Space.hasPointwiseRightKanExtension_restrictionFunctor_op`
from the representability datum alone, exactly as in the source, where `i_F` is produced by the
lemma itself and no smallness condition is in force. -/
theorem restrictionSheafFunctor_eq_restrictionToposHom_inverseImage
    (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    letI := hasPointwiseRightKanExtension_restrictionFunctor_op B S hS F p e
    restrictionSheafFunctor B S hS F p hp e =
      (restrictionToposHom B S hS F p hp e).inverseImage :=
  rfl

/-- The displayed computation of equation 075K, `π_{F,*}ℱ(U) = ℱ(u(U))` which the notation
abbreviates: the sections of the direct image over an étale chart `U` of `F` are the sections of
`ℱ` over the object `u(U)` of `𝒳`. -/
theorem projectionPushforward_obj_obj (hp : p.IsFiberedInGroupoids)
    (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (U : SmallEtale B S hS F) :
    ((projectionPushforward B S hS F p hp hF e).obj 𝓕).obj.obj (Opposite.op U) =
      𝓕.obj.obj (Opposite.op ((restrictionFunctor B S hS F p e).obj U)) :=
  rfl

end RingedTopoi

end AlgebraicGeometry.Space

end
