module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackExtensionMap
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackChartObstructionIdealSquare

/-!
# Naturality of the difference of lifts along a morphism of split thickenings

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'` and `h₂ : T ⟶ T'₂` first
order thickenings with retractions `r`, `r₂`, and `g : T'₂ ⟶ T'` a morphism under `T` with
`r₂ = g ≫ r`. The class on `X_T` of a lift `L` across `h`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass`) is the class of the short
exact sequence `0 ⟶ I ⊗ i_*𝒢 ⟶ 𝒢' ⟶ i_*𝒢 ⟶ 0` of `L` read through `ρ_* = (X_r)_*`, the
identification `ρ_* i_*𝒢 ≅ 𝒢` of its quotient and that of its kernel with `𝒢 ⊗ f_T^*𝒥`. A morphism
from this sequence to the direct image along `X_g` of the sequence of a lift across `h₂` computes
the class of the latter from that of `L`, as soon as it is compatible with these identifications.
For the pullback of `L` along `g`, the compatibility on the quotients is the associativity
coherence of Stacks 03LU.

This is a step of the naturality of the tangent spaces in the second proof of Stacks 08WA.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass_eq_comp_of_hom`: a morphism of
  extensions computes the class of a lift.
* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftQuotientIso_inv`: `ρ_* i_*𝒢 ≅ 𝒢` is the
  identification `i_* ⋙ ρ_* ≅ 𝟭` at `𝒢`.
* `map_pullbackQuotientMap_comp_hom_app_eq_thickeningLiftQuotientIso` (in the namespace
  `AlgebraicGeometry.Space.CoherentSituation`): the compatibility on the quotients for the pullback
  of a lift.

## Implementation notes

Two spellings of the same objects meet here: the terms of the short exact sequences of lifts and
the identification of the quotient on one side, and the direct images of modules
`(smallEtaleRingedToposHom B S hS _).pushforwardModules` of the coherence of Stacks 03LU
(`AlgebraicGeometry.Space.CoherentSituation.retractionPushforwardModulesIso_hom_app_pullback`) on
the other. The kernel unfolds the direct images when it compares their actions on morphisms, or the
components of their comparisons, at objects spelled differently (more than a million heartbeats).
The two are therefore joined by
`CategoryTheory.map_comp_hom_app_eq_inv_comp_hom_of_heq`, stated over arbitrary categories with
the objects related by equations and the morphisms by `HEq`, and instantiated once with `rfl` and
`heq_of_eq`: every remaining comparison is between objects or between hom types. The comparison
`ρ_*(X_g)_* ≅ ρ₂_*` and the quotient map are taken up to equations, so that a caller passes its own
spelling of them.

The identifications of the quotient are stated in a section without the `HasExt` instances of the
first one: a theorem carries every instance of its section whose variables it uses, and at a use
instance search for these `Ext` structures times out.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

-- TC for (smallEtaleRingedTopos X).J.HasSheafCompose (forget RingCat) exceeds 1000
-- heartbeats below priority 10000
attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

universe e u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

attribute [local instance] preservesFiniteColimits_structureRestrict_relativeMap
  preservesFiniteLimits_structureRestrict_relativeMap

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (hfl : IsFlat B S hS (D.projection T').hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]

/-- The short exact sequence `0 ⟶ I ⊗ i_*𝒢 ⟶ 𝒢' ⟶ i_*𝒢 ⟶ 0` of the extension attached to a
lift (`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension`). -/
abbrev thickeningLiftShortComplex (h : ξ.T ⟶ T')
    (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
    (L : D.ThickeningLift ξ h) :=
  ShortComplex.mk (thickeningLiftExtension h hh L).f (thickeningLiftExtension h hh L).g
    (yonedaExtension_comp_zero _)

/-- `ρ_*(I ⊗ i_*𝒢) ≅ 𝒢 ⊗ f_T^*𝒥`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningKernelRetractionIso`), with its source
written through the short exact sequence of a lift. -/
def thickeningLiftKernelIso (hr : h ≫ r = 𝟙 ξ.T)
    (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
    (hfl : IsFlat B S hS (D.projection T').hom) (L : D.ThickeningLift ξ h) :
    (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules.obj
        (thickeningLiftShortComplex h hh L).X₁ ≅ thickeningCoefficient ξ h hh :=
  thickeningKernelRetractionIso h r hr hh hfl

/-- `𝒢 ≅ ρ_* i_*𝒢` (`AlgebraicGeometry.Space.CoherentSituation.thickenedModuleRetractionIso`),
with its target written through the short exact sequence of a lift. -/
def thickeningLiftQuotientIso (hr : h ≫ r = 𝟙 ξ.T)
    (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
    (L : D.ThickeningLift ξ h) :
    objectToposModule ξ ≅
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules.obj
        (thickeningLiftShortComplex h hh L).X₃ :=
  (thickenedModuleRetractionIso h r hr).symm

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))] in
/-- The class on `X_T` of a lift, as the class of its short exact sequence read through `ρ_*`. -/
theorem thickeningLiftExtClass_eq_extConj (L : D.ThickeningLift ξ h) :
    haveI := preservesFiniteLimits_retraction_pushforwardModules (D := D) r
    haveI := preservesFiniteColimits_retraction_pushforwardModules h r hr hh
    thickeningLiftExtClass h r hr hh hfl L =
      Stacks.Homology.extConj (thickeningLiftQuotientIso hr hh L).hom
        (thickeningLiftKernelIso hr hh hfl L).hom
        ((yonedaExtension_shortExact (thickeningLiftExtension h hh L)).extClass.mapExactFunctor
          (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap r)).pushforwardModules) := by
  unfold thickeningLiftExtClass retractionExt thickeningLiftExtensionClass extensionClass
  rfl

/-- `ρ_*(X_g)_* ≅ ρ₂_*` for the retractions `ρ = X_r`, `ρ₂ = X_{r₂}` with `r₂ = g ≫ r`. -/
abbrev retractionCompIso (g : T'₂ ⟶ T') (hgr : r₂ = g ≫ r) :=
  pushforwardModulesCompAt B S hS (D.relativeSquareSituation.relativeMap g)
      (D.relativeSquareSituation.relativeMap r) ≪≫
    eqToIso (congrArg (fun x : D.relativeSquareSituation.space T'₂ ⟶
        D.relativeSquareSituation.space ξ.T =>
      (smallEtaleRingedToposHom B S hS x).pushforwardModules)
      (relativeMap_comp_of_eq_comp g hgr))

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))] in
include hr₂ hh₂ in
/-- **A morphism of extensions computes the class of a lift.** -/
theorem thickeningLiftExtClass_eq_comp_of_hom (g : T'₂ ⟶ T')
    (c : (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules ⋙
        (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules ≅
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r₂)).pushforwardModules)
    (L : D.ThickeningLift ξ h) (L₂ : D.ThickeningLift ξ h₂)
    (κ : thickeningCoefficient ξ h hh ⟶ thickeningCoefficient ξ h₂ hh₂)
    (τ₁ : (thickeningLiftShortComplex h hh L).X₁ ⟶
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.obj
        (thickeningLiftShortComplex h₂ hh₂ L₂).X₁)
    (τ₂ : (thickeningLiftShortComplex h hh L).X₂ ⟶
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.obj
        (thickeningLiftShortComplex h₂ hh₂ L₂).X₂)
    (τ₃ : (thickeningLiftShortComplex h hh L).X₃ ⟶
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.obj
        (thickeningLiftShortComplex h₂ hh₂ L₂).X₃)
    (comm₁₂ : (thickeningLiftShortComplex h hh L).f ≫ τ₂ = τ₁ ≫
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
        (thickeningLiftShortComplex h₂ hh₂ L₂).f)
    (comm₂₃ : (thickeningLiftShortComplex h hh L).g ≫ τ₃ = τ₂ ≫
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
        (thickeningLiftShortComplex h₂ hh₂ L₂).g)
    (h₁ : (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map τ₁ ≫
        c.hom.app (thickeningLiftShortComplex h₂ hh₂ L₂).X₁ =
      (thickeningLiftKernelIso hr hh hfl L).hom ≫ κ ≫ (thickeningLiftKernelIso hr₂ hh₂ hfl₂ L₂).inv)
    (h₃ : (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map τ₃ ≫
        c.hom.app (thickeningLiftShortComplex h₂ hh₂ L₂).X₃ =
      (thickeningLiftQuotientIso hr hh L).inv ≫ (thickeningLiftQuotientIso hr₂ hh₂ L₂).hom) :
    thickeningLiftExtClass h₂ r₂ hr₂ hh₂ hfl₂ L₂ =
      (thickeningLiftExtClass h r hr hh hfl L).comp (Abelian.Ext.mk₀ κ) (add_zero 1) := by
  have := preservesFiniteLimits_retraction_pushforwardModules (D := D) r
  have := preservesFiniteColimits_retraction_pushforwardModules h r hr hh
  have := preservesFiniteLimits_retraction_pushforwardModules (D := D) r₂
  have := preservesFiniteColimits_retraction_pushforwardModules h₂ r₂ hr₂ hh₂
  refine (thickeningLiftExtClass_eq_extConj hr₂ hh₂ hfl₂ L₂).trans (Eq.trans ?_
    (congrArg (fun x => Abelian.Ext.comp x (Abelian.Ext.mk₀ κ) (add_zero 1))
      (thickeningLiftExtClass_eq_extConj hr hh hfl L).symm))
  exact Stacks.Homology.extConj_mapExactFunctor_extClass_naturality
    (S₁ := thickeningLiftShortComplex h hh L) (S₂ := thickeningLiftShortComplex h₂ hh₂ L₂)
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap r)).pushforwardModules
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap r₂)).pushforwardModules
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap g)).pushforwardModules
    c
    (yonedaExtension_shortExact (thickeningLiftExtension h hh L))
    (yonedaExtension_shortExact (thickeningLiftExtension h₂ hh₂ L₂))
    τ₁ τ₂ τ₃ comm₁₂ comm₂₃
    (thickeningLiftQuotientIso hr hh L) (thickeningLiftQuotientIso hr₂ hh₂ L₂)
    (thickeningLiftKernelIso hr hh hfl L) (thickeningLiftKernelIso hr₂ hh₂ hfl₂ L₂) κ h₁ h₃

end AlgebraicGeometry.Space.CoherentSituation

namespace CategoryTheory

/-- If `ρ.hom ≫ F(e) = φ` for an isomorphism `ρ` and `e' ≫ e = 𝟙`, then `F(e') ≫ ρ⁻¹` is a section
of `φ`. -/
theorem map_comp_inv_comp_eq_id_of_hom_comp_map_eq {C D : Type*} {_ : Category C}
    {_ : Category D} (F : D ⥤ C) {P Q : D} {W : C} (e' : P ⟶ Q) (e : Q ⟶ P) (he : e' ≫ e = 𝟙 P)
    (ρ : W ≅ F.obj Q) {φ : W ⟶ F.obj P} (hφ : ρ.hom ≫ F.map e = φ) :
    (F.map e' ≫ ρ.inv) ≫ φ = 𝟙 (F.obj P) := by
  rw [← hφ, Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp, he, F.map_id]

/-- **A map read through identifications `I ⋙ R ≅ 𝟭`, `I₂ ⋙ R₂ ≅ 𝟭` along a comparison
`G ⋙ R ≅ R₂`**: if `R(φ)` followed by `R(I M) ≅ M` is the comparison at `I₂ M` followed by
`R₂(I₂ M) ≅ M`, and `τ : I M ⟶ G(I₂ M)` is a section of `φ`, then `R(τ)` followed by the
comparison is `R(I M) ≅ M ≅ R₂(I₂ M)`. It is stated for objects `X₁`, `X₂` equal to `I M`,
`I₂ M`, with `τ`, `q⁻¹`, `q₂⁻¹` given up to these equalities. -/
theorem map_comp_hom_app_eq_inv_comp_hom_of_heq {C₀ C₁ C₂ : Type*} {_ : Category C₀}
    {_ : Category C₁} {_ : Category C₂} {I : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {I₂ : C₀ ⥤ C₂}
    {R₂ : C₂ ⥤ C₀} {G : C₂ ⥤ C₁} {α : I ⋙ R ≅ 𝟭 C₀} {α₂ : I₂ ⋙ R₂ ≅ 𝟭 C₀}
    {c : G ⋙ R ≅ R₂} {M : C₀} {φ : (I₂ ⋙ G).obj M ⟶ I.obj M}
    (coh : @CategoryStruct.comp _ _ (R.obj ((I₂ ⋙ G).obj M)) (R.obj (I.obj M)) ((𝟭 C₀).obj M)
        (R.map φ) (α.hom.app M) =
      @CategoryStruct.comp _ _ ((G ⋙ R).obj (I₂.obj M)) (R₂.obj (I₂.obj M)) ((𝟭 C₀).obj M)
        (c.hom.app (I₂.obj M)) (α₂.hom.app M))
    {X₁ : C₁} {X₂ : C₂} (e₁ : I.obj M = X₁) (e₂ : I₂.obj M = X₂)
    {τ : I.obj M ⟶ G.obj (I₂.obj M)} (hτ : τ ≫ φ = 𝟙 (I.obj M))
    (τ₃ : X₁ ⟶ G.obj X₂) (hτ₃ : HEq τ₃ τ) (q : M ≅ R.obj X₁) (hq : HEq q.inv (α.hom.app M))
    (q₂ : M ≅ R₂.obj X₂) (hq₂ : HEq q₂.inv (α₂.hom.app M)) :
    R.map τ₃ ≫ c.hom.app X₂ = q.inv ≫ q₂.hom := by
  subst e₁ e₂
  obtain rfl := eq_of_heq hτ₃
  have hq' : q.inv = α.hom.app M := eq_of_heq hq
  have hq₂' : q₂.inv = α₂.hom.app M := eq_of_heq hq₂
  rw [← hq', ← hq₂'] at coh
  have hc : c.hom.app (I₂.obj M) = R.map φ ≫ q.inv ≫ q₂.hom := by
    rw [← Category.assoc, coh, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hc, ← Category.assoc, ← R.map_comp, hτ, R.map_id, Category.id_comp]

end CategoryTheory

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

attribute [local instance] preservesFiniteColimits_structureRestrict_relativeMap
  preservesFiniteLimits_structureRestrict_relativeMap

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))

/-- `AlgebraicGeometry.Space.CoherentSituation.thickenedRetractionIso` is
`AlgebraicGeometry.Space.CoherentSituation.retractionPushforwardModulesIso`. -/
theorem thickenedRetractionIso_eq :
    thickenedRetractionIso (D := D) h r hr = retractionPushforwardModulesIso h r hr :=
  rfl

/-- The components of `AlgebraicGeometry.Space.CoherentSituation.thickenedRetractionIso` are those
of `AlgebraicGeometry.Space.CoherentSituation.retractionPushforwardModulesIso`. -/
theorem thickenedRetractionIso_hom_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)) :
    (thickenedRetractionIso h r hr).hom.app M =
      (retractionPushforwardModulesIso h r hr).hom.app M :=
  congrArg (fun e => e.hom.app M) (thickenedRetractionIso_eq hr)

/-- `ρ_* i_*𝒢 ≅ 𝒢` of a lift is the identification `i_* ⋙ ρ_* ≅ 𝟭` at `𝒢`. -/
theorem thickeningLiftQuotientIso_inv (L : D.ThickeningLift ξ h) :
    (thickeningLiftQuotientIso hr hh L).inv =
      (retractionPushforwardModulesIso h r hr).hom.app (objectToposModule ξ) :=
  thickenedRetractionIso_hom_app hr (objectToposModule ξ)

include hr hr₂ hh hh₂ in
/-- **The quotient identification along the pullback of a lift, read on `X_T`.** Let
`g : T'₂ ⟶ T'` be a morphism under `T` (`h₂ ≫ g = h`) with retractions `r`, `r₂ = g ≫ r`, and `L`
a lift of `ξ` across `h`. The direct image under `ρ = X_r` of the quotient map
`τ₃ : i_*𝒢 ≅ Ψ₀ i₂_*𝒢 ≅ (X_g)_* i₂_*𝒢` of the extensions attached to `L` and to its pullback,
followed by the comparison `ρ_*(X_g)_* ≅ ρ₂_*` of Stacks 03LU, is `ρ_* i_*𝒢 ≅ 𝒢 ≅ ρ₂_* i₂_*𝒢`,
the quotient identifications of the two lifts
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftQuotientIso`). This is the hypothesis on
the quotients of `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass_eq_comp_of_hom`
for that morphism of extensions; `τ₃` and the comparison are taken up to equations. -/
theorem map_pullbackQuotientMap_comp_hom_app_eq_thickeningLiftQuotientIso (g : T'₂ ⟶ T')
    (hg : h₂ ≫ g = h) (hgr : r₂ = g ≫ r) (L : D.ThickeningLift ξ h)
    (c : (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules ⋙
        (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules ≅
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r₂)).pushforwardModules)
    (hc : c = pushforwardModulesCompAt B S hS (D.relativeSquareSituation.relativeMap g)
        (D.relativeSquareSituation.relativeMap r) ≪≫
      eqToIso (congrArg (fun x : D.relativeSquareSituation.space T'₂ ⟶
          D.relativeSquareSituation.space ξ.T =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules)
        (relativeMap_comp_of_eq_comp g hgr)))
    (τ₃ : (thickeningLiftShortComplex h hh L).X₃ ⟶
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.obj
        (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).X₃)
    (hτ₃ : τ₃ = (structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h))).map
        ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).inv.app (objectToposModule ξ)) ≫
      ((smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj (objectToposModule ξ))).inv) :
    (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map τ₃ ≫
        c.hom.app (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).X₃ =
      (thickeningLiftQuotientIso hr hh L).inv ≫
        (thickeningLiftQuotientIso hr₂ hh₂ (L.pullback g hg)).hom := by
  subst hc
  have hcoh :=
    retractionPushforwardModulesIso_hom_app_pullback g hg hr hr₂ hgr (objectToposModule ξ)
  have hsec := map_comp_inv_comp_eq_id_of_hom_comp_map_eq
      (structureRestrict (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)))
      ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).inv.app (objectToposModule ξ))
      ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).hom.app (objectToposModule ξ))
      ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).inv_hom_id_app (objectToposModule ξ))
      ((smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj (objectToposModule ξ)))
      (restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_eq
        (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
        (relativeMap_comp_of_comp_eq g hg) (objectToposModule ξ))
  have key := map_comp_hom_app_eq_inv_comp_hom_of_heq hcoh
    (X₁ := (thickeningLiftShortComplex h hh L).X₃)
    (X₂ := (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).X₃) rfl rfl hsec
  exact key τ₃ (heq_of_eq hτ₃) (thickeningLiftQuotientIso hr hh L)
    (heq_of_eq (thickeningLiftQuotientIso_inv hr hh L))
    (thickeningLiftQuotientIso hr₂ hh₂ (L.pullback g hg))
    (heq_of_eq (thickeningLiftQuotientIso_inv hr₂ hh₂ (L.pullback g hg)))

end AlgebraicGeometry.Space.CoherentSituation

end
