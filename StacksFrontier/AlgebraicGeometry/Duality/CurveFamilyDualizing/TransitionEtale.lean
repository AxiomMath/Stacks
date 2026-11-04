module

public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.TransitionChart
public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.TransitionEtaleFlat
public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.TransitionEtalePerfect
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCompositeDiagonal
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekEtale

/-!
# Transition isomorphisms along étale morphisms

Let `f : Y ⟶ T` and `f' : X' ⟶ T` be flat and locally of finite presentation and let
`e : X' ⟶ Y` be étale with `e ≫ f = f'`. Then the square `(e, 𝟙_T)` has a transition isomorphism
`Le^*ω^•_{Y/T} ≅ ω^•_{X'/T}` (`AlgebraicGeometry.Scheme.Hom.hasRelDualizingTransition_of_etale`):
the pullback of the chosen relative dualizing complex of `f`, with the transported map `ξ`, is a
relative dualizing complex for `f'`. This is the étale localisation of relative dualizing
complexes used in Duality for Spaces.

## The proof

Since `e` is étale, its diagonal `X' ⟶ X' ×_Y X'` is an open immersion, so `X'` itself is a
diagonal open of `e` (`Stacks.Duality.etaleDiagonalOpen`). The diagonal open of
the composite `e ≫ f` built in the proof of Stacks 0E30
(`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.comp`) is an open `W'` of `X' ×_T X'` on which
`e × e` lands in the coborder diagonal open `W` of `f`, is flat, and makes the square of the
diagonals `X' ⟶ W'`, `Y ⟶ W` cartesian. Its trace `O` on the coborder diagonal open of `f'`
inherits all of this. On `O` the transported pair is a relative dualizing complex: the relative
perfectness of `Le^*K` is `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_comp_derivedPullback`,
and the diagonal condition is flat base change for sheaf Hom with exact support (Stacks 0E2M,
`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isRelativeDualizingComplex_xiTransport_of_flat`).
Stacks 0E2W then provides the transition.

As a consequence every chart square has a transition isomorphism
(`AlgebraicGeometry.Scheme.Hom.ChartSquare.hasRelDualizingTransition`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Duality.TwistedInverseImageDuality

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

/-- The standard model of `D(𝒪_T)`, for `letI`. -/
local macro "stdᴰ[" T:term "]" : term =>
  `(HasDerivedCategory.standard (StrictlyPerfect.OXMod $T))

/-- The standard models of `D(𝒪_{T|_U})` for all opens `U` of `T`, for `letI`. -/
local macro "stdOpens[" T:term "]" : term =>
  `(fun (U : TopologicalSpace.Opens ($T).carrier) =>
    HasDerivedCategory.standard (StrictlyPerfect.OXMod (($T).restrict U.isOpenEmbedding)))

/-- The map `X' ⟶ Y` of the diagonal open of a composite built from the diagonal open
`Stacks.Duality.etaleDiagonalOpen e` of an étale morphism is `e`. -/
theorem etaleDiagonalOpen_compBaseMap {X' Y : Scheme.{u}} (e : X' ⟶ Y) [Etale e] :
    (Stacks.Duality.etaleDiagonalOpen e).compBaseMap = e := by
  change pullback.diagonal e ≫ pullback.fst e e ≫ e = e
  rw [pullback.diagonal_fst_assoc]

section Etale

variable {Y T X' : Scheme.{u}} (f : Y ⟶ T) [Flat f] [LocallyOfFinitePresentation f]
  (e : X' ⟶ Y) [Etale e] [Flat (e ≫ f)] [LocallyOfFinitePresentation (e ≫ f)]

/-- The open of the coborder diagonal open of `e ≫ f` traced by the diagonal open of the
composite built from the coborder diagonal open of `f` and
`Stacks.Duality.etaleDiagonalOpen e`. -/
def etaleOpen : (DiagonalOpen.coborder (e ≫ f)).W.Opens :=
  (DiagonalOpen.coborder (e ≫ f)).ι ⁻¹ᵁ
    ((DiagonalOpen.coborder f).compOpen (Stacks.Duality.etaleDiagonalOpen e))

/-- The diagonal of a diagonal open of `e ≫ f`, followed by its inclusion, is the diagonal of `e`
followed by `compMap`. -/
private theorem diag_ι_eq_diagonalOpen_ι_comp_compMap {Y T X' : Scheme.{u}} (f : Y ⟶ T)
    (e : X' ⟶ Y) [Etale e] (D : DiagonalOpen (e ≫ f)) :
    D.diag ≫ D.ι = (Stacks.Duality.etaleDiagonalOpen e).ι ≫ DiagonalOpen.compMap f e := by
  rw [D.fac, ← DiagonalOpen.diagonal_comp_compMap]

omit [Flat f] [LocallyOfFinitePresentation f] [Flat (e ≫ f)]
  [LocallyOfFinitePresentation (e ≫ f)] in
/-- `etaleOpen` contains the diagonal. -/
theorem range_diag_subset_etaleOpen :
    Set.range (DiagonalOpen.coborder (e ≫ f)).diag ⊆ etaleOpen f e := by
  rintro _ ⟨x, rfl⟩
  change (DiagonalOpen.coborder (e ≫ f)).ι ((DiagonalOpen.coborder (e ≫ f)).diag x) ∈
    (DiagonalOpen.coborder f).compOpen (Stacks.Duality.etaleDiagonalOpen e)
  have h₂ : (Stacks.Duality.etaleDiagonalOpen e).ι x ∈
      DiagonalOpen.compMap f e ⁻¹ᵁ
        (DiagonalOpen.coborder f).compOpen (Stacks.Duality.etaleDiagonalOpen e) := by
    rw [DiagonalOpen.compMap_preimage_compOpen]
    exact ⟨x, rfl⟩
  rw [← Scheme.Hom.comp_apply, diag_ι_eq_diagonalOpen_ι_comp_compMap, Scheme.Hom.comp_apply]
  exact h₂

/-- The diagonal open of `e ≫ f` on which the transition is checked. -/
abbrev etaleTransitionOpen : DiagonalOpen (e ≫ f) :=
  coborderOpen (e ≫ f) (etaleOpen f e) (range_diag_subset_etaleOpen f e)

/-- The inclusion of `etaleTransitionOpen` into the diagonal open of the composite. -/
def etaleOpenInclusion :
    (etaleTransitionOpen f e).W ⟶
      ((DiagonalOpen.coborder f).compOpen (Stacks.Duality.etaleDiagonalOpen e)).toScheme :=
  IsOpenImmersion.lift ((DiagonalOpen.coborder f).compOpen (Stacks.Duality.etaleDiagonalOpen e)).ι
    (etaleTransitionOpen f e).ι (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.2)

omit [Flat f] [LocallyOfFinitePresentation f] [Flat (e ≫ f)]
  [LocallyOfFinitePresentation (e ≫ f)] in
/-- `etaleOpenInclusion` followed by the inclusion of the diagonal open of the composite is the
inclusion of `etaleTransitionOpen`. -/
theorem etaleOpenInclusion_ι :
    etaleOpenInclusion f e ≫
        ((DiagonalOpen.coborder f).compOpen (Stacks.Duality.etaleDiagonalOpen e)).ι =
      (etaleTransitionOpen f e).ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- `etaleOpenInclusion` is an open immersion. -/
instance : IsOpenImmersion (etaleOpenInclusion f e) := by
  unfold etaleOpenInclusion
  infer_instance

/-- `e × e`, restricted to `etaleTransitionOpen`, landing in the coborder diagonal open of `f`. -/
def etaleW : (etaleTransitionOpen f e).W ⟶ (DiagonalOpen.coborder f).W :=
  etaleOpenInclusion f e ≫ (DiagonalOpen.coborder f).compProd (Stacks.Duality.etaleDiagonalOpen e)

omit [Flat f] [LocallyOfFinitePresentation f] [Flat (e ≫ f)]
  [LocallyOfFinitePresentation (e ≫ f)] in
/-- `etaleW` followed by the inclusion of the coborder diagonal open of `f` is the inclusion of
`etaleTransitionOpen` followed by the product map `squareProd`. -/
theorem etaleW_ι (comm : e ≫ f = (e ≫ f) ≫ 𝟙 T) :
    etaleW f e ≫ (DiagonalOpen.coborder f).ι =
      (etaleTransitionOpen f e).ι ≫ squareProd f (e ≫ f) e (𝟙 T) comm := by
  rw [etaleW, Category.assoc, DiagonalOpen.compProd_ι, ← Category.assoc, etaleOpenInclusion_ι]

omit [Flat f] [LocallyOfFinitePresentation f] [Flat (e ≫ f)]
  [LocallyOfFinitePresentation (e ≫ f)] in
/-- The diagonal of `etaleTransitionOpen` followed by the inclusion is the closed immersion
`δ` of the diagonal open of the composite. -/
theorem diag_etaleOpenInclusion :
    (etaleTransitionOpen f e).diag ≫ etaleOpenInclusion f e =
      (DiagonalOpen.coborder f).compδ (Stacks.Duality.etaleDiagonalOpen e) := by
  rw [← cancel_mono ((DiagonalOpen.coborder f).compOpen (Stacks.Duality.etaleDiagonalOpen e)).ι,
    Category.assoc, etaleOpenInclusion_ι, DiagonalOpen.compδ_ι,
    diag_ι_eq_diagonalOpen_ι_comp_compMap]

omit [Flat f] [LocallyOfFinitePresentation f] [Flat (e ≫ f)]
  [LocallyOfFinitePresentation (e ≫ f)] in
/-- **The diagonal square of `e` is cartesian** on `etaleTransitionOpen`. -/
theorem isPullback_etaleW :
    IsPullback (etaleTransitionOpen f e).diag e (etaleW f e) (DiagonalOpen.coborder f).diag := by
  have hH : Set.range ((DiagonalOpen.coborder f).compδ (Stacks.Duality.etaleDiagonalOpen e)) ⊆
      Set.range (etaleOpenInclusion f e) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(etaleTransitionOpen f e).diag x, ?_⟩
    rw [← Scheme.Hom.comp_apply, diag_etaleOpenInclusion]
  have h₁ := IsOpenImmersion.isPullback_lift_id
    ((DiagonalOpen.coborder f).compδ (Stacks.Duality.etaleDiagonalOpen e))
    (etaleOpenInclusion f e) hH
  have hl : IsOpenImmersion.lift (etaleOpenInclusion f e)
      ((DiagonalOpen.coborder f).compδ (Stacks.Duality.etaleDiagonalOpen e)) hH =
        (etaleTransitionOpen f e).diag := by
    rw [← cancel_mono (etaleOpenInclusion f e), IsOpenImmersion.lift_fac,
      diag_etaleOpenInclusion]
  rw [hl] at h₁
  have h₂ := ((DiagonalOpen.coborder f).isPullback_compδ (Stacks.Duality.etaleDiagonalOpen e)).flip
  rw [etaleDiagonalOpen_compBaseMap] at h₂
  have h₃ := h₁.paste_vert h₂
  rw [Category.id_comp] at h₃
  exact h₃

/-- The morphism `etaleW` is flat. -/
instance : Flat (etaleW f e) := by
  have := (DiagonalOpen.coborder f).flat_compProd (Stacks.Duality.etaleDiagonalOpen e)
  unfold etaleW
  infer_instance

/-- **The transported pair is a relative dualizing complex on `etaleTransitionOpen`**, through any
identification of the diagonal objects. -/
theorem isRelativeDualizingComplex_etale (comm : e ≫ f = (e ≫ f) ≫ 𝟙 T)
    (eΔ : (pull (etaleW f e)).obj (DiagonalOpen.coborder f).diagonalObject ≅
      (etaleTransitionOpen f e).diagonalObject) :
    letI := stdᴰ[RingedSpace.inverseImage T.toRingedSpace (e ≫ f).base]
    letI := stdOpens[RingedSpace.inverseImage T.toRingedSpace (e ≫ f).base]
    IsRelativeDualizingComplex (e ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage T.toRingedSpace (e ≫ f).base)) (etaleTransitionOpen f e)
      (DiagonalOpen.baseChangeComplex e (relDualizingComplex f))
      ((DiagonalOpen.coborder f).xiTransport (etaleTransitionOpen f e) e (etaleW f e)
        (DiagonalOpen.proj_of_squareProd (etaleW_ι f e comm)) eΔ _ (relDualizingMap f)) :=
  let := stdᴰ[RingedSpace.inverseImage T.toRingedSpace f.base]
  let := stdOpens[RingedSpace.inverseImage T.toRingedSpace f.base]
  letI := stdᴰ[RingedSpace.inverseImage T.toRingedSpace (e ≫ f).base]
  letI := stdOpens[RingedSpace.inverseImage T.toRingedSpace (e ≫ f).base]
  (DiagonalOpen.coborder f).isRelativeDualizingComplex_xiTransport_of_flat
    (etaleTransitionOpen f e) (isPullback_etaleW f e) _ (isRelativeDualizingComplex_relDualizing f)
    (isPerfectRelativeTo_comp_derivedPullback f e _
      (isRelativeDualizingComplex_relDualizing f).isPerfectRelativeTo) eΔ

/-- `hasRelDualizingTransition_of_etale` with `f' = e ≫ f`. -/
theorem hasRelDualizingTransition_of_etale_comp (comm : e ≫ f = (e ≫ f) ≫ 𝟙 T) :
    HasRelDualizingTransition e (𝟙 T) comm := by
  have hasw : DiagonalOpen.HasDiagIso (DiagonalOpen.coborder f) (etaleTransitionOpen f e)
      (etaleW f e) :=
    ⟨(DiagonalOpen.coborder f).flatDiagIso (etaleTransitionOpen f e) (isPullback_etaleW f e)
      (torIndependent_of_flat_right _ _)⟩
  exact exists_isRelDualizingTransition_of_isRelativeDualizingComplex (etaleOpen f e)
    (range_diag_subset_etaleOpen f e) (etaleW f e) (etaleW_ι f e comm) hasw
    (isRelativeDualizingComplex_etale f e comm _)

end Etale

/-- **Transition isomorphisms along étale morphisms.** For `f : Y ⟶ T` and `f' : X' ⟶ T` flat and
locally of finite presentation and `e : X' ⟶ Y` étale with `e ≫ f = f'`, the square `(e, 𝟙_T)`
has a transition isomorphism `Le^*ω^•_{Y/T} ≅ ω^•_{X'/T}`: the pullback of the chosen relative
dualizing complex of `f`, with the transported map `ξ`, is a relative dualizing complex for `f'`
on an open of the coborder diagonal open of `f'` containing the diagonal. -/
theorem hasRelDualizingTransition_of_etale {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T}
    [Flat fY] [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f']
    (e : X' ⟶ Y) [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T) :
    HasRelDualizingTransition e (𝟙 T) comm := by
  have hf : e ≫ fY = f' := comm.trans (Category.comp_id _)
  subst hf
  exact hasRelDualizingTransition_of_etale_comp fY e comm

/-- **Every chart square has a transition isomorphism**: its étale gap square has one. -/
theorem ChartSquare.hasRelDualizingTransition {X S X' S' : Scheme.{u}} {f : X ⟶ S}
    {f' : X' ⟶ S'} [Flat f] [LocallyOfFinitePresentation f] [Flat f']
    [LocallyOfFinitePresentation f'] (sq : ChartSquare f f') :
    HasRelDualizingTransition sq.g' sq.g sq.comm :=
  sq.hasRelDualizingTransition_of_gap (hasRelDualizingTransition_of_etale sq.gap sq.gap_comm)

end AlgebraicGeometry.Scheme.Hom

end
