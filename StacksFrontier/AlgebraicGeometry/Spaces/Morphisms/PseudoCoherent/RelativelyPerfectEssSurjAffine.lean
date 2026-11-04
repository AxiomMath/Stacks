module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentAffineModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectEssSurjReduction

/-!
# The affine case of the essential surjectivity in Stacks 0DKW

In Situation 0DKU, essential surjectivity in Stacks 0DKW was reduced to the case where the space
over the chosen stage is affine, with structure morphism through an étale morphism `V ⟶ Y₀` from
an affine algebraic space
(`RelativeDescentSituation.relativelyPerfectEssentiallySurjective_of_affine`). This file moves
essential surjectivity along isomorphisms of the source data, and so reads it, when the space
`X₀` over the chosen stage is affine, `e₀ : h_{Z'} ≅ X₀`, on the *model* source data whose stages
and limit are the represented presheaves `h_{Wⱼ}` and `h_W` of a representation `R` of the base
changes along `e₀ ≫ p₀`.

## Main definitions

* `RelativeDescentSituation.modelSourceData`: the model source data.

## Main results

* `RelativeDescentSituation.relativelyPerfectEssentiallySurjective_of_sourceIso`:
  essential surjectivity transports along isomorphisms of the stages and of the limit over the
  inverse system.
* `RelativeDescentSituation.relativelyPerfectEssentiallySurjective_of_modelSourceData`:
  essential surjectivity from that of the model.

## References

* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DI8](https://stacks.math.columbia.edu/tag/0DI8)
* [Stacks Project, Tag 0DKQ](https://stacks.math.columbia.edu/tag/0DKQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u v

namespace AlgebraicGeometry.Space.RelativeDescentSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

section SourceIso

attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

local notation "𝐋" f => smallEtaleDerivedModulePullback _ _ _ f
local notation "𝐏" => DerivedPullbackComposition.canonical _ _ _

/-- Relative perfectness transports along an isomorphism of the source over the target: for an
isomorphism `a : X' ≅ X` and `f : X ⟶ Y`, the derived pullback along `a` of a `Y`-perfect object
is `Y`-perfect along `a ≫ f`.  This is Stacks 0DKT at the cartesian square with sides `a` and the
identity of `Y`. -/
theorem isPerfectAlong_pull_of_iso {X X' Y : AlgebraicSpaces B S hS} (a : X' ≅ X) (f : X ⟶ Y)
    (f' : X' ⟶ Y) (ha : a.hom ≫ f = f') (hfl : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) (hfl' : IsFlat B S hS f'.hom)
    (hlfp' : IsLocallyOfFinitePresentation B S hS f'.hom) (E : derivedModules B S hS X)
    (hE : IsPerfectAlong f hfl hlfp E) :
    IsPerfectAlong f' hfl' hlfp' (((smallEtaleDerivedPullbackData B S hS).pull a.hom).obj E) :=
  relativelyPerfectBaseChangeStable B S hS f (𝟙 Y) a.hom f'
    (IsPullback.of_horiz_isIso ⟨by rw [ha, Category.comp_id]⟩) hfl hlfp hfl' hlfp' E hE

/-- **Essential surjectivity transports along isomorphisms of the source data.**  Let `F` and
`F'` be source data over the inverse system of `D`, with isomorphisms of the limits and of the
stages compatible with the structure morphisms and with the projections.  If the situation of `F'`
is essentially surjective, so is that of `F`. -/
theorem relativelyPerfectEssentiallySurjective_of_sourceIso
    (F F' : SourceData B S hS D.Y D.limitCone D.i₀)
    (aX : (D.withSource F').limitSource ≅ (D.withSource F).limitSource)
    (haX : aX.hom ≫ (D.withSource F).limitStructure = (D.withSource F').limitStructure)
    (aS : ∀ i : D.LaterIndex, (D.withSource F').stageSource i ≅ (D.withSource F).stageSource i)
    (haS : ∀ i : D.LaterIndex,
      (aS i).hom ≫ (D.withSource F).stageStructure i = (D.withSource F').stageStructure i)
    (hπ : ∀ i : D.LaterIndex, aX.hom ≫ (D.withSource F).sourceProjection i =
      (D.withSource F').sourceProjection i ≫ (aS i).hom)
    (h : (D.withSource F').RelativelyPerfectEssentiallySurjective) :
    (D.withSource F).RelativelyPerfectEssentiallySurjective := by
  intro hD E₀ hE
  obtain ⟨E, hE₀⟩ : ∃ E : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (D.withSource F).limitSource)), E = E₀ := ⟨E₀, rfl⟩
  subst hE₀
  have hE' := isPerfectAlong_pull_of_iso aX (D.withSource F).limitStructure
    (D.withSource F').limitStructure haX _ _ (D.withSource F').isFlat_limitStructure
    (D.withSource F').isLocallyOfFinitePresentation_limitStructure E hE
  obtain ⟨i, E', hE'i, ⟨φ⟩⟩ := h (isSchemeLimit_withSource (D.withSource F) F' hD) _ hE'
  obtain ⟨Eᵢ, hEᵢ⟩ : ∃ Eᵢ : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS ((D.withSource F').stageSource i))), Eᵢ = E' :=
    ⟨E', rfl⟩
  subst hEᵢ
  refine ⟨i, (𝐋 (aS i).inv).obj Eᵢ, ?_, ?_⟩
  · refine isPerfectAlong_pull_of_iso (aS i).symm ((D.withSource F').stageStructure i)
      ((D.withSource F).stageStructure i) ?_ _ _ _ _ Eᵢ hE'i
    rw [Iso.symm_hom, Iso.inv_comp_eq, haS]
  · have hk : (D.withSource F).sourceProjection i ≫ (aS i).inv =
        aX.inv ≫ (D.withSource F').sourceProjection i := by
      rw [Iso.comp_inv_eq, Category.assoc, ← hπ, Iso.inv_hom_id_assoc]
    exact ⟨((𝐏).iso _ _ _ hk).app Eᵢ ≪≫ ((𝐏).iso _ _ _ rfl).symm.app Eᵢ ≪≫
      (𝐋 aX.inv).mapIso φ ≪≫ ((𝐏).iso aX.inv aX.hom (𝟙 _) aX.inv_hom_id).app E ≪≫
      ((𝐏).idIso _).app E⟩

variable {D} in
/-- **The model source data of a situation with affine `X₀`.**  For source data `F` over the
inverse system of `D`, `e₀ : h_{Z'} ≅ F.X₀` with `Z'` affine, and a representation `R` of the base
changes along `e₀ ≫ p₀`: the same space over the chosen stage, with the represented presheaves
`h_{Wⱼ}` and `h_W` of `R` as the base changes to the stages and to the limit, and the morphisms of
the site induced by `R` as transitions and projections. -/
def modelSourceData (F : SourceData B S hS D.Y D.limitCone D.i₀) {Z' : BigAffineFppf B S hS}
    (e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅ F.X₀)
    (R : (D.withSource F).AffineBaseChangeRepresentation Z' (e₀.hom ≫ F.p₀)) :
    SourceData B S hS D.Y D.limitCone D.i₀ where
  X₀ := F.X₀
  p₀ := F.p₀
  initial_isAlgebraicSpace := F.initial_isAlgebraicSpace
  initial_isFlat := F.initial_isFlat
  initial_isFinitePresentation := F.initial_isFinitePresentation
  Xᵢ i hi := yoneda.obj (R.W.obj (op ⟨i, hi⟩))
  stageX_isAlgebraicSpace i hi := isAlgebraicSpace_yoneda B S hS _
  toX₀ i hi := yoneda.map (R.q ⟨i, hi⟩) ≫ e₀.hom
  toYᵢ i hi := R.p ⟨i, hi⟩
  stage_isPullback i hi := (D.withSource F).stageModel_isPullback e₀ R ⟨i, hi⟩
  fᵢⱼ i j hi hj hij := yoneda.map (R.W.map (homOfLE (show (⟨i, hi⟩ : D.LaterIndex) ≤ ⟨j, hj⟩
    from hij)).op)
  fᵢⱼ_toYᵢ i j hi hj hij := R.map_p ⟨i, hi⟩ ⟨j, hj⟩ hij
  fᵢⱼ_toX₀ i j hi hj hij := by
    rw [← Category.assoc, ← Functor.map_comp, R.map_q]
  X := yoneda.obj R.c.pt
  X_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS _
  toInitial := yoneda.map R.qc ≫ e₀.hom
  toLimit := R.pc
  limit_isPullback := (D.withSource F).limitModel_isPullback e₀ R
  fᵢ i hi := yoneda.map (R.c.π.app (op ⟨i, hi⟩))
  fᵢ_toYᵢ i hi := R.π_p ⟨i, hi⟩
  fᵢ_toX₀ i hi := by
    rw [← Category.assoc, ← Functor.map_comp, R.π_q]

/-- **Essential surjectivity of a situation with affine `X₀`, from that of its model.**  The
stages and the limit of the situation are identified with those of the model source data
(`AlgebraicGeometry.Space.RelativeDescentSituation.stageModelIso`, `limitModelIso`). -/
theorem relativelyPerfectEssentiallySurjective_of_modelSourceData
    (F : SourceData B S hS D.Y D.limitCone D.i₀) {Z' : BigAffineFppf B S hS}
    (e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅ F.X₀)
    (R : (D.withSource F).AffineBaseChangeRepresentation Z' (e₀.hom ≫ F.p₀))
    (h : (D.withSource (modelSourceData F e₀ R)).RelativelyPerfectEssentiallySurjective) :
    (D.withSource F).RelativelyPerfectEssentiallySurjective :=
  D.relativelyPerfectEssentiallySurjective_of_sourceIso F (modelSourceData F e₀ R)
    (ObjectProperty.isoMk _ ((D.withSource F).limitModelIso e₀ R))
    (ObjectProperty.hom_ext _ ((D.withSource F).limitModelIso_hom_toLimit e₀ R))
    (fun i => ObjectProperty.isoMk _ ((D.withSource F).stageModelIso e₀ R i))
    (fun i => ObjectProperty.hom_ext _ ((D.withSource F).stageModelIso_hom_toYᵢ e₀ R i))
    (fun i => ObjectProperty.hom_ext _ ((D.withSource F).limitModelIso_hom_fᵢ e₀ R i)) h

end SourceIso

end AlgebraicGeometry.Space.RelativeDescentSituation

end
