module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom.LimitSystemColimBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssSurjCanonicalPullbackData

/-!
# The affine case of Stacks 09RI, reduced to the base-changed system over an étale chart

In Situation 09RH let `u : U ⟶ X₀` be an étale morphism of algebraic spaces onto the chosen
stage.  The stages of the base-changed system
`AlgebraicGeometry.Space.DescentSituation.baseChangeSystem` of `u` are the fibre products
`U_i = X_i ×_{X₀} U`, and each square

```
U_i --u_i--> X_i
|f_i'        |f_{i0}
v            v
U   --u-->   X₀
```

is cartesian with `u` and `u_i` étale.  For `A ∈ D(𝒪_U)` and `K₀ ∈ D(𝒪_{X₀})` the base change
map for derived extension by zero is therefore invertible at `A`
(`AlgebraicGeometry.Space.isIso_extensionByZeroBaseChange_canonical_app_of_isPullback`), so the
localization map

`Hom_{D(𝒪_{X_i})}(Lf_{i0}^*(u_!A), Lf_{i0}^*K₀) ⟶ Hom_{D(𝒪_{U_i})}(Lf_i'^*A, Lf_i'^*(Lu^*K₀))`

of `AlgebraicGeometry.Space.DerivedPullbackComposition.localizationHom` is bijective, and the
same at the vertex.  The localization maps commute with the maps attached to the factorisations
(`AlgebraicGeometry.Space.DerivedPullbackComposition.localizationHom_factorHom`), which for this
system are exactly the transition maps and the maps to the vertex.  Hence the colimit statement
of the tag for `(u_!A, K₀)` on the system of `X₀` **is** the colimit statement for
`(A, Lu^*K₀)` on the base-changed system over `U`.

That is the reduction of the affine case of Stacks 09RI to a statement over an affine base: taking
`A = Lu^*E₀` and `U` affine, the hypothesis of
`AlgebraicGeometry.Space.DescentSituation.isColim_of_affine` becomes the colimit statement for the
system of the fibre products `U_i = X_i ×_{X₀} U` over the affine `U`.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.stageLocalizationHom` and `limitLocalizationHom`:
  the localization maps of the base change of Situation 09RH along `u`, at a stage and at the
  vertex.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.isPullback_baseChangeStage` and
  `isPullback_baseChangeLimit`: the defining squares of the base-changed stages and vertex are
  cartesian.
* `AlgebraicGeometry.Space.DescentSituation.isEtale_baseChangeToStage` and
  `isEtale_baseChangeToLimitSpace`: the projections `U_i ⟶ X_i` and `X ×_{X₀} U ⟶ X` are étale,
  being base changes of `u`.
* `AlgebraicGeometry.Space.DescentSituation.bijective_stageLocalizationHom` and
  `bijective_limitLocalizationHom`: **the localization maps are bijective**, with the base change
  hypothesis discharged.
* `AlgebraicGeometry.Space.DescentSituation.stageLocalizationHom_trans` and
  `limitLocalizationHom_projHom`: **the localization maps are compatible with the transition maps
  of the two systems and with their maps to the vertex.**
* `AlgebraicGeometry.Space.DescentSituation.isColim_lowerShriek_of_baseChangeSystem`: **the
  colimit statement for `(u_!A, K₀)` over `X₀` from the colimit statement for `(A, Lu^*K₀)` over
  `U`**.

## Implementation notes

The statements are for the pullback-pseudofunctor datum
`AlgebraicGeometry.Space.canonicalPullbackData`, whose composition comparison is the one of
Stacks 0D6D that
`AlgebraicGeometry.Space.DerivedPullbackComposition.extensionByZeroBaseChange` and
`localizationHom` are built from.  The datum
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` of
`AlgebraicGeometry.Space.DescentSituation.ExtendRestrictIsColim` has the same inverse images but
the *universal* comparison of the total left derived functor along a composite as its composition
comparison, and the two comparisons are not definitionally equal; identifying them is not done
here, and is what the statements below would need in order to be read at that datum.

The compatibility of a localization map with the maps attached to factorisations is a single
instance of
`AlgebraicGeometry.Space.DerivedPullbackComposition.localizationHom_factorHom` in each of the two
cases, the morphism of squares being the base change of a transition morphism
(`AlgebraicGeometry.Space.DescentSituation.baseChangeTransition_comp_toStage`) and the base change
of a projection (`baseChangeProjection_comp_toStage`).

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe w v u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The map of morphism sets attached to a factorisation for
`AlgebraicGeometry.Space.canonicalPullbackData` is the one of the canonical pseudofunctoriality
datum**: both are conjugation by the identification of the factorisation. -/
theorem factorHom_canonicalPullbackData {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : X ⟶ Z} (h : f ≫ g = k) (K L : derivedModules B S hS Z)
    (φ : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L) :
    PullbackData.factorHom (canonicalPullbackData B S hS) h (X := K) (Y := L) φ =
      (DerivedPullbackComposition.canonical B S hS).factorHom f g k h K L φ := by
  subst h
  show Functor.conjHom ((canonicalPullbackData B S hS).triangle (f := f) (g := g) rfl) φ = _
  rw [PullbackData.triangle_rfl]
  rfl

variable {b : AlgebraicSpaces B S hS} {J : Type w} [Preorder J]

/-- The transition map of a system for `AlgebraicGeometry.Space.canonicalPullbackData` is the
map attached to the factorisation `t_{ij} ≫ k_i = k_j` of the canonical pseudofunctoriality
datum. -/
theorem trans_eq_factorHom_canonical
    (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) b J)
    (X Y : derivedModules B S hS b) (i j : J) (h : i ≤ j)
    (φ : ((canonicalPullbackData B S hS).pull (Sys.toBase i)).obj X ⟶
      ((canonicalPullbackData B S hS).pull (Sys.toBase i)).obj Y) :
    Sys.trans (canonicalPullbackData B S hS) X Y i j h φ =
      (DerivedPullbackComposition.canonical B S hS).factorHom (Sys.transition h) (Sys.toBase i)
        (Sys.toBase j) (Sys.transition_toBase h) X Y φ :=
  factorHom_canonicalPullbackData (Sys.transition_toBase h) X Y φ

/-- The map to the vertex of a system for `AlgebraicGeometry.Space.canonicalPullbackData` is the
map attached to the factorisation `p_j ≫ k_j = k` of the canonical pseudofunctoriality datum. -/
theorem projHom_eq_factorHom_canonical
    (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) b J)
    (X Y : derivedModules B S hS b) (j : J)
    (φ : ((canonicalPullbackData B S hS).pull (Sys.toBase j)).obj X ⟶
      ((canonicalPullbackData B S hS).pull (Sys.toBase j)).obj Y) :
    Sys.projHom (canonicalPullbackData B S hS) X Y j φ =
      (DerivedPullbackComposition.canonical B S hS).factorHom (Sys.proj j) (Sys.toBase j)
        Sys.limitToBase (Sys.proj_toBase j) X Y φ :=
  factorHom_canonicalPullbackData (Sys.proj_toBase j) X Y φ

/-- The localization map of a cartesian square with étale `u` and `u'` is bijective. -/
private theorem bijective_localizationHom_of_isPullback {T T' U Z : AlgebraicSpaces B S hS}
    (u' : T' ⟶ T) (t : T ⟶ Z) (t' : T' ⟶ U) (u : U ⟶ Z) (sq : IsPullback u' t' t u)
    (hu : IsEtale B S hS u.hom) (hu' : IsEtale B S hS u'.hom) (A : derivedModules B S hS U)
    (K : derivedModules B S hS Z) :
    Function.Bijective
      ((DerivedPullbackComposition.canonical B S hS).localizationHom u' t t' u hu sq.w A K) :=
  have := isIso_extensionByZeroBaseChange_canonical_app_of_isPullback u' t t' u sq hu hu' A
  (DerivedPullbackComposition.canonical B S hS).bijective_localizationHom u' t t' u hu hu' sq.w
    A K

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {U : AlgebraicSpaces B S hS}

/-! ### The base-changed stages are fibre products -/

/-- **A stage of the base change of Situation 09RH along `u` is the fibre product
`U_i = X_i ×_{X₀} U`**, as a cartesian square. -/
theorem isPullback_baseChangeStage (u : U ⟶ D.stage D.base) (i : D.Stages) :
    IsPullback (baseChangeToStage u i) (baseChangeToBase u i) (D.transition i.2) u :=
  IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) (IsPullback.of_hasPullback _ _)

/-- **The vertex of the base change of Situation 09RH along `u` is the fibre product
`X ×_{X₀} U`**, as a cartesian square. -/
theorem isPullback_baseChangeLimit (u : U ⟶ D.stage D.base) :
    IsPullback (baseChangeToLimitSpace (D := D) u) (baseChangeLimitToBase (D := D) u)
      (D.projection D.base) u :=
  IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) (IsPullback.of_hasPullback _ _)

/-- **The projection `U_i ⟶ X_i` is étale**, being a base change of the étale `u`. -/
theorem isEtale_baseChangeToStage {u : U ⟶ D.stage D.base} (hu : IsEtale B S hS u.hom)
    (i : D.Stages) : IsEtale B S hS (baseChangeToStage u i).hom :=
  isEtale_of_isPullback B S hS (baseChangeToBase u i) (baseChangeToStage u i) u
    (D.transition i.2) (isPullback_baseChangeStage u i).flip hu

/-- **The projection `X ×_{X₀} U ⟶ X` is étale**, being a base change of the étale `u`. -/
theorem isEtale_baseChangeToLimitSpace {u : U ⟶ D.stage D.base} (hu : IsEtale B S hS u.hom) :
    IsEtale B S hS (baseChangeToLimitSpace (D := D) u).hom :=
  isEtale_of_isPullback B S hS (baseChangeLimitToBase (D := D) u)
    (baseChangeToLimitSpace (D := D) u) u (D.projection D.base)
    (isPullback_baseChangeLimit u).flip hu

/-! ### The localization maps -/

variable (u : U ⟶ D.stage D.base) (hu : IsEtale B S hS u.hom) (A : derivedModules B S hS U)
  (K₀ : derivedModules B S hS (D.stage D.base))

/-- **The localization map at a stage of the base change of Situation 09RH along `u`**, from
`Hom_{D(𝒪_{X_i})}(Lf_{i0}^*(u_!A), Lf_{i0}^*K₀)` to
`Hom_{D(𝒪_{U_i})}(Lf_i'^*A, Lf_i'^*(Lu^*K₀))`. -/
abbrev stageLocalizationHom (i : D.Stages) :=
  (DerivedPullbackComposition.canonical B S hS).localizationHom (baseChangeToStage u i)
    (D.transition i.2) (baseChangeToBase u i) u hu (isPullback_baseChangeStage u i).w A K₀

/-- **The localization map at the vertex of the base change of Situation 09RH along `u`.** -/
abbrev limitLocalizationHom :=
  (DerivedPullbackComposition.canonical B S hS).localizationHom
    (baseChangeToLimitSpace (D := D) u) (D.projection D.base) (baseChangeLimitToBase (D := D) u) u
    hu (isPullback_baseChangeLimit u).w A K₀

/-- **The localization map at a stage is bijective**: the base change map for extension by zero
along the cartesian square of the stage is invertible. -/
theorem bijective_stageLocalizationHom (i : D.Stages) :
    Function.Bijective (stageLocalizationHom u hu A K₀ i) :=
  bijective_localizationHom_of_isPullback _ _ _ _ (isPullback_baseChangeStage u i) hu
    (isEtale_baseChangeToStage hu i) A K₀

/-- **The localization map at the vertex is bijective.** -/
theorem bijective_limitLocalizationHom :
    Function.Bijective (limitLocalizationHom u hu A K₀) :=
  bijective_localizationHom_of_isPullback _ _ _ _ (isPullback_baseChangeLimit u) hu
    (isEtale_baseChangeToLimitSpace hu) A K₀

/-! ### Compatibility with the transition maps -/

/-- **The localization maps are compatible with the transition maps of the two systems**: the
transition map of the system of `X₀` at `(u_!A, K₀)` followed by the localization map at the later
stage is the localization map at the earlier stage followed by the transition map of the
base-changed system at `(A, Lu^*K₀)`. -/
theorem stageLocalizationHom_trans {i j : D.Stages} (h : i ≤ j)
    (χ : ((canonicalPullbackData B S hS).pull (D.limitSystem.toBase i)).obj
        ((etaleExtensionByZero B S hS u hu).mapDerivedCategory.obj A) ⟶
      ((canonicalPullbackData B S hS).pull (D.limitSystem.toBase i)).obj K₀) :
    stageLocalizationHom u hu A K₀ j
        (D.limitSystem.trans (canonicalPullbackData B S hS) _ K₀ i j h χ) =
      (baseChangeSystem u).trans (canonicalPullbackData B S hS) A
        ((smallEtaleDerivedModulePullback B S hS u).obj K₀) i j h
        (stageLocalizationHom u hu A K₀ i χ) := by
  rw [trans_eq_factorHom_canonical D.limitSystem
      ((etaleExtensionByZero B S hS u hu).mapDerivedCategory.obj A) K₀ i j h χ,
    trans_eq_factorHom_canonical (baseChangeSystem u) A
      ((smallEtaleDerivedModulePullback B S hS u).obj K₀) i j h
      (stageLocalizationHom u hu A K₀ i χ)]
  exact (DerivedPullbackComposition.canonical B S hS).localizationHom_factorHom
    (baseChangeToStage u i) (baseChangeToStage u j) (D.transition i.2) (D.transition j.2)
    (baseChangeToBase u i) (baseChangeToBase u j) u hu (isPullback_baseChangeStage u i).w
    (isPullback_baseChangeStage u j).w (D.transition (show i.1 ≤ j.1 from h))
    (baseChangeTransition u h) (D.transition_comp i.2 h j.2)
    (baseChangeTransition_comp_toBase u h) (baseChangeTransition_comp_toStage u h) A K₀ χ

/-- **The localization maps are compatible with the maps to the vertex of the two systems.** -/
theorem limitLocalizationHom_projHom (i : D.Stages)
    (χ : ((canonicalPullbackData B S hS).pull (D.limitSystem.toBase i)).obj
        ((etaleExtensionByZero B S hS u hu).mapDerivedCategory.obj A) ⟶
      ((canonicalPullbackData B S hS).pull (D.limitSystem.toBase i)).obj K₀) :
    limitLocalizationHom u hu A K₀
        (D.limitSystem.projHom (canonicalPullbackData B S hS) _ K₀ i χ) =
      (baseChangeSystem u).projHom (canonicalPullbackData B S hS) A
        ((smallEtaleDerivedModulePullback B S hS u).obj K₀) i
        (stageLocalizationHom u hu A K₀ i χ) := by
  rw [projHom_eq_factorHom_canonical D.limitSystem
      ((etaleExtensionByZero B S hS u hu).mapDerivedCategory.obj A) K₀ i χ,
    projHom_eq_factorHom_canonical (baseChangeSystem u) A
      ((smallEtaleDerivedModulePullback B S hS u).obj K₀) i
      (stageLocalizationHom u hu A K₀ i χ)]
  exact (DerivedPullbackComposition.canonical B S hS).localizationHom_factorHom
    (baseChangeToStage u i) (baseChangeToLimitSpace (D := D) u) (D.transition i.2)
    (D.projection D.base) (baseChangeToBase u i) (baseChangeLimitToBase (D := D) u) u hu
    (isPullback_baseChangeStage u i).w (isPullback_baseChangeLimit u).w (D.projection i.1)
    (baseChangeProjection u i) (D.projection_comp_transition i.2)
    (baseChangeProjection_comp_toBase u i) (baseChangeProjection_comp_toStage u i) A K₀ χ

/-! ### The reduction -/

/-- **The colimit statement of Stacks 09RI for `(u_!A, K₀)` on the system of `X₀`, from the
colimit statement for `(A, Lu^*K₀)` on the base-changed system over `U`**, for an étale
`u : U ⟶ X₀`.

This is the reduction of the affine case of the tag to a statement over `U`: the hypothesis
`hleaf` of `AlgebraicGeometry.Space.DescentSituation.isColim_of_affine` asks for the colimit
statement for `u_!(Lu^*E₀)` against `K₀`, and this derives it from the colimit statement for
`Lu^*E₀` against `Lu^*K₀` on the system of the fibre products `U_i = X_i ×_{X₀} U` over `U`,
which for `U` affine is the affine case proper. -/
theorem isColim_lowerShriek_of_baseChangeSystem
    (h : (baseChangeSystem u).IsColim (canonicalPullbackData B S hS) A
      ((smallEtaleDerivedModulePullback B S hS u).obj K₀)) :
    D.limitSystem.IsColim (canonicalPullbackData B S hS)
      ((etaleExtensionByZero B S hS u hu).mapDerivedCategory.obj A) K₀ :=
  Stacks.IsStagesColimit.ofEquiv _ _
    (fun i ↦ Equiv.ofBijective _ (bijective_stageLocalizationHom u hu A K₀ i))
    (Equiv.ofBijective _ (bijective_limitLocalizationHom u hu A K₀))
    (fun _ _ hij s ↦ stageLocalizationHom_trans u hu A K₀ hij s)
    (fun i s ↦ limitLocalizationHom_projHom u hu A K₀ i s) h

end DescentSituation

end AlgebraicGeometry.Space

end
