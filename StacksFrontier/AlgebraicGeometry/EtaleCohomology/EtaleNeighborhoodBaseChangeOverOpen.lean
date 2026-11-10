module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleNeighborhoodOpenSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# The base change to the strict henselization as a directed limit over an open neighbourhood

Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S` and `U` an open subscheme
of `S` containing the image of `s`. Write `X_U = X ×_S U` for the restriction of `f` over `U`.
This file presents `X ×_S Spec(𝒪^{sh}_{S,s})` as the limit of the base changes `Z_a ×_U X_U`
over a nonempty directed partial order `α`, where `Z : αᵒᵖ ⥤ Over U` runs through a cofinal
system of affine étale neighbourhoods of `s` lying over `U`. With `U = Spec A` affine this is the
setting of [Stacks, Tag 03Q6].

## Main definitions

* `AlgebraicGeometry.etaleNeighborhoodDirectedIndex` — the chosen directed partial order, with its
  initial functor `AlgebraicGeometry.etaleNeighborhoodDirectedFunctor` to the affine étale
  neighbourhoods of `s` over `U`.
* `AlgebraicGeometry.etaleNeighborhoodDirectedSystem` — the system `Z : αᵒᵖ ⥤ Over U`.
* `AlgebraicGeometry.sourceOverOpen` — `X_U = X ×_S U`, as a scheme over `U`.
* `AlgebraicGeometry.etaleNeighborhoodDirectedBaseChangeCone` — the cone on
  `a ↦ Z_a ×_U X_U` with vertex `Spec(𝒪^{sh}_{S,s}) ×_U X_U`.
* `AlgebraicGeometry.etaleNeighborhoodDirectedBaseChangeConePtIso` — that vertex is
  `X ×_S Spec(𝒪^{sh}_{S,s})`.

## Main results

* `AlgebraicGeometry.isLimitEtaleNeighborhoodDirectedBaseChangeCone` — the cone is a limit cone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (U : S.Opens) (hU : s.hom (closedPoint s.residueField) ∈ U)

/-- The chosen nonempty directed partial order indexing a cofinal system of affine étale
neighbourhoods of `s` over `U`. -/
def etaleNeighborhoodDirectedIndex : Type u :=
  (exists_directed_etaleNeighborhoodOpenIndex B S hS s U hU).choose

/-- The partial order on `etaleNeighborhoodDirectedIndex`. -/
instance : PartialOrder (etaleNeighborhoodDirectedIndex B S hS s U hU) :=
  (exists_directed_etaleNeighborhoodOpenIndex B S hS s U hU).choose_spec.choose

/-- The index `etaleNeighborhoodDirectedIndex` is directed. -/
instance : IsDirected (etaleNeighborhoodDirectedIndex B S hS s U hU) (· ≤ ·) :=
  (exists_directed_etaleNeighborhoodOpenIndex B S hS s U hU).choose_spec.choose_spec.choose

/-- The index `etaleNeighborhoodDirectedIndex` is nonempty. -/
instance : Nonempty (etaleNeighborhoodDirectedIndex B S hS s U hU) :=
  (exists_directed_etaleNeighborhoodOpenIndex B S hS s U
    hU).choose_spec.choose_spec.choose_spec.choose

/-- The initial functor from the directed index to the affine étale neighbourhoods of `s` over
`U`. -/
def etaleNeighborhoodDirectedFunctor :
    (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ ⥤ etaleNeighborhoodOpenIndex B S hS s U :=
  (exists_directed_etaleNeighborhoodOpenIndex B S hS s U
    hU).choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- The functor `etaleNeighborhoodDirectedFunctor` is initial. -/
instance initial_etaleNeighborhoodDirectedFunctor :
    (etaleNeighborhoodDirectedFunctor B S hS s U hU).Initial :=
  (exists_directed_etaleNeighborhoodOpenIndex B S hS s U
    hU).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

/-- **The directed system of affine étale neighbourhoods of `s` over `U`**, as schemes over
`U`. -/
abbrev etaleNeighborhoodDirectedSystem :
    (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ ⥤ Over (U : Scheme.{u}) :=
  etaleNeighborhoodDirectedFunctor B S hS s U hU ⋙ etaleNeighborhoodOpenOverDiagram B S hS s U

/-- Each scheme of the directed system `etaleNeighborhoodDirectedSystem` is affine. -/
instance (a : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ) :
    IsAffine ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).left :=
  inferInstanceAs (IsAffine ((etaleNeighborhoodAffineDiagram B S hS s).obj
    ((etaleNeighborhoodDirectedFunctor B S hS s U hU).obj a).1))

/-- The strict henselization over `U`, as a cone on the directed system. -/
abbrev strictHenselizationDirectedCone : Cone (etaleNeighborhoodDirectedSystem B S hS s U hU) :=
  (strictHenselizationOpenOverCone B S hS s U hU).whisker
    (etaleNeighborhoodDirectedFunctor B S hS s U hU)

/-- The strict henselization is the limit, over `U`, of the directed system. -/
def isLimitStrictHenselizationDirectedCone :
    IsLimit (strictHenselizationDirectedCone B S hS s U hU) :=
  (Functor.Initial.isLimitWhiskerEquiv (etaleNeighborhoodDirectedFunctor B S hS s U hU) _).symm
    (isLimitStrictHenselizationOpenOverCone B S hS s U hU)

/-! ### The base changes -/

variable {X : Scheme.{u}} (f : X ⟶ S)

/-- The restriction `X_U = X ×_S U` of `f` over `U`, as a scheme over `U`. -/
abbrev sourceOverOpen : Over (U : Scheme.{u}) :=
  Over.mk (pullback.snd f U.ι)

/-- The directed system of base changes `a ↦ Z_a ×_U X_U`. -/
abbrev etaleNeighborhoodDirectedBaseChange :
    (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ ⥤ Scheme.{u} :=
  (etaleNeighborhoodDirectedSystem B S hS s U hU ⋙
    Over.pullback (sourceOverOpen S U f).hom) ⋙ Over.forget (sourceOverOpen S U f).left

/-- The cone on the base changes with vertex `Spec(𝒪^{sh}_{S,s}) ×_U X_U`. -/
abbrev etaleNeighborhoodDirectedBaseChangeCone :
    Cone (etaleNeighborhoodDirectedBaseChange B S hS s U hU f) :=
  (Over.forget (sourceOverOpen S U f).left).mapCone
    ((Over.pullback (sourceOverOpen S U f).hom).mapCone
      (strictHenselizationDirectedCone B S hS s U hU))

/-- **`Spec(𝒪^{sh}_{S,s}) ×_U X_U` is the limit of the base changes `Z_a ×_U X_U`**. -/
def isLimitEtaleNeighborhoodDirectedBaseChangeCone :
    IsLimit (etaleNeighborhoodDirectedBaseChangeCone B S hS s U hU f) :=
  haveI : IsConnected (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ :=
    IsCofiltered.isConnected _
  isLimitOfPreserves (Over.forget (sourceOverOpen S U f).left)
    (isLimitOfPreserves (Over.pullback (sourceOverOpen S U f).hom)
      (isLimitStrictHenselizationDirectedCone B S hS s U hU))

/-- The vertex `Spec(𝒪^{sh}_{S,s}) ×_U X_U` of the cone is isomorphic to
`X ×_S Spec(𝒪^{sh}_{S,s})`. -/
def etaleNeighborhoodDirectedBaseChangeConePtIso :
    (etaleNeighborhoodDirectedBaseChangeCone B S hS s U hU f).pt ≅
      strictHenselizationBaseChange B hS f s :=
  pullbackSymmetry _ _ ≪≫
    pullbackLeftPullbackSndIso f U.ι (strictHenselizationToOpen B S hS s U hU) ≪≫
    pullback.congrHom rfl (strictHenselizationToOpen_ι B S hS s U hU)

/-- The identification of the vertex with `X ×_S Spec(𝒪^{sh}_{S,s})` lies over `X`: followed by the
projection `p` it is the projection of `Spec(𝒪^{sh}_{S,s}) ×_U X_U` to `X_U ⟶ X`. -/
@[reassoc (attr := simp)]
theorem etaleNeighborhoodDirectedBaseChangeConePtIso_hom_toSource :
    (etaleNeighborhoodDirectedBaseChangeConePtIso B S hS s U hU f).hom ≫
        strictHenselizationBaseChangeToSource B hS f s =
      pullback.snd _ _ ≫ pullback.fst f U.ι := by
  change (pullbackSymmetry (strictHenselizationToOpen B S hS s U hU) (pullback.snd f U.ι)).hom ≫
      (pullbackLeftPullbackSndIso f U.ι (strictHenselizationToOpen B S hS s U hU)).hom ≫
        (pullback.congrHom (f₁ := f) rfl (strictHenselizationToOpen_ι B S hS s U hU)).hom ≫
          pullback.fst f (strictHenselizationToBase B S hS s) =
      pullback.snd (strictHenselizationToOpen B S hS s U hU) (pullback.snd f U.ι) ≫
        pullback.fst f U.ι
  rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst, pullbackSymmetry_hom_comp_fst_assoc]

/-- The identification of the vertex with `X ×_S Spec(𝒪^{sh}_{S,s})` lies over the strict
henselization. -/
@[reassoc (attr := simp)]
theorem etaleNeighborhoodDirectedBaseChangeConePtIso_hom_toStrictHenselization :
    (etaleNeighborhoodDirectedBaseChangeConePtIso B S hS s U hU f).hom ≫
        strictHenselizationBaseChangeToStrictHenselization B hS f s =
      pullback.fst _ _ := by
  change (pullbackSymmetry (strictHenselizationToOpen B S hS s U hU) (pullback.snd f U.ι)).hom ≫
      (pullbackLeftPullbackSndIso f U.ι (strictHenselizationToOpen B S hS s U hU)).hom ≫
        (pullback.congrHom (f₁ := f) rfl (strictHenselizationToOpen_ι B S hS s U hU)).hom ≫
          pullback.snd f (strictHenselizationToBase B S hS s) =
      pullback.fst (strictHenselizationToOpen B S hS s U hU) (pullback.snd f U.ι)
  rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd, pullbackSymmetry_hom_comp_snd]

/-- If `f` is quasi-compact, so is its restriction `X_U ⟶ U`. -/
instance [QuasiCompact f] : QuasiCompact (sourceOverOpen S U f).hom := by
  dsimp only [sourceOverOpen, Over.mk_hom]
  infer_instance

/-- If `f` is quasi-separated, so is its restriction `X_U ⟶ U`. -/
instance [QuasiSeparated f] : QuasiSeparated (sourceOverOpen S U f).hom := by
  dsimp only [sourceOverOpen, Over.mk_hom]
  infer_instance

end AlgebraicGeometry

end
