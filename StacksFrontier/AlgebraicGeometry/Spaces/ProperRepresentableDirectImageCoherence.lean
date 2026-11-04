module

public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct images of coherent modules along proper representable morphisms

Let `f : X ⟶ Y` be a representable proper morphism of algebraic spaces over a scheme `S`
contained in a big fppf site `B`, with `Y` locally Noetherian, and let `𝓕` be a coherent
`𝒪_X`-module.  Then `f_*𝓕` is a coherent `𝒪_Y`-module.

Over an affine étale chart `A` of `Y` the sections of `f_*𝓕` are the sections of `𝓕` over the
base change `T = A ×_Y X`, which is an étale chart of `X` whose scheme is proper over the scheme
of `A`, because `f` is representable.  Those are the global sections of the chart restriction of
`𝓕` to the scheme of `T`, a coherent module there, and the global sections of a coherent module
on a scheme proper over an affine Noetherian scheme are a finite module over the functions on
the base, by Stacks 02O6 in degree zero.  Coherence of `f_*𝓕` then follows from quasi-coherence
(Stacks 03M9) and the affine-chart criterion of Stacks 07UB.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_restrictScalars_appTop_sectionsTop`: global sections of a
  coherent module on a scheme proper over an affine Noetherian scheme are finite over the base.
* `AlgebraicGeometry.Space.moduleFinite_modulePushforward_val_obj_of_isProper`: the sections of
  `f_*𝓕` over an affine chart of `Y` are finite over the functions on the chart.
* `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isProper`: `f_*𝓕` is coherent.
* `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite'`: **the coherence assertion
  of Stacks 07UH** — the direct image of a coherent module along a finite morphism onto a
  locally Noetherian algebraic space is coherent; a finite morphism is representable and
  proper (Stacks 04NZ).

## Implementation notes

The chart restriction used is `AlgebraicGeometry.Space.chartRestrictionSheaf`, whose sections
over the open `⊤` of the chart's scheme are, on the nose, the sections of `𝓕` over the chart that
open cuts out, with scalars changed along the structure sheaf applied to the inclusion of that
chart into `T` (`AlgebraicGeometry.Space.structureRingSheaf_map_chartOpensTopHom`).  That
inclusion is an isomorphism, so the sections of `𝓕` over `T` are identified with the global
sections of the chart restriction, semilinearly along the pullback of functions from the scheme
of `A`; its coherence is that of the isomorphic
`AlgebraicGeometry.Space.chartSchemeModule`.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 04NZ](https://stacks.math.columbia.edu/tag/04NZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Global sections over a proper scheme -/

/-- Finiteness of a module restricted along a ring map transfers across an isomorphism. -/
private theorem moduleFinite_restrictScalars_of_iso {R R' : Type*} [Ring R] [CommRing R']
    (φ : R' →+* R) {M N : ModuleCat.{u} R} (e : M ≅ N)
    [Module.Finite R' ((ModuleCat.restrictScalars φ).obj M)] :
    Module.Finite R' ((ModuleCat.restrictScalars φ).obj N) :=
  Module.Finite.equiv ((ModuleCat.restrictScalars φ).mapIso e).toLinearEquiv

/-- **The global sections of a coherent module on a scheme proper over an affine Noetherian
scheme are a finite module over the functions on the base.**  This is Stacks 02O6 in degree zero,
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, read through the
identification of the degree-zero right derived functor of global sections with global
sections. -/
@[ega "II 7.3.12" "more general"]
theorem moduleFinite_restrictScalars_appTop_sectionsTop {T A : Scheme.{u}} (g : T ⟶ A)
    [_root_.AlgebraicGeometry.IsProper g] [IsAffine A] [IsLocallyNoetherian A] (N : T.Modules)
    [N.IsCoherent] :
    Module.Finite Γ(A, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj (N.val.obj (op ⊤))) := by
  have := ProperCoherenceWitness.moduleFinite_cohomology g N 0
  exact moduleFinite_restrictScalars_of_iso g.appTop.hom
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerivedZeroIsoSelf.app N)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Sections over an affine chart of the target -/

/-- **The base change of a proper representable morphism to an étale chart of the target is a
proper morphism of schemes.** -/
theorem isProper_toScheme_smallBaseChangeProjection (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (hfp : IsProper B S hS f.hom)
    (A : SmallEtale B S hS Y.1) :
    _root_.AlgebraicGeometry.IsProper
      ((BigFppfOver.toScheme B S hS).map ((smallBaseChangeProjection B S hS f hf).app A)) :=
  ((presheaf_isProper_iff B S hS f.hom X.2 Y.2 hf).1 hfp).property _ _ _ (hf.isPullback A.1.hom)

/-- **The sections of the direct image along a proper representable morphism over an affine
chart of the target are finite.**  Let `f : X ⟶ Y` be representable and proper, with `Y` locally
Noetherian, and let `𝓕` be coherent.  Then for every étale chart `A` of `Y` with affine scheme the
sections of `f_*𝓕` over `A` form a finite module over the functions on `A`. -/
theorem moduleFinite_modulePushforward_val_obj_of_isProper (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (hfp : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M)
    (A : SmallEtale B S hS Y.1) (hA : IsAffine (chartScheme A)) :
    Module.Finite (chartRing B S hS Y.1 Y.2 A)
      (((modulePushforward B S hS f).obj M).val.obj (op A)) := by
  refine Stacks.SheafOfModules.moduleFinite_sections_of_iso
    ((modulePushforwardChartIso B S hS f hf).app M) A ?_
  let T' := (smallBaseChange B S hS f hf).obj A
  let g₀ := (BigFppfOver.toScheme B S hS).map ((smallBaseChangeProjection B S hS f hf).app A)
  have : _root_.AlgebraicGeometry.IsProper g₀ :=
    isProper_toScheme_smallBaseChangeProjection B S hS f hf hfp A
  have : IsLocallyNoetherian (chartScheme A) := isLocallyNoetherian_chart B S hS hY A
  have : (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite T').IsCoherent :=
    isCoherent_chartSchemeModule_of_isLocallyNoetherian B S hS X M hM T'
      (isLocallyNoetherian_chart B S hS
        (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 Y.2 f.hom hfp.2.1.1 hY) T')
  have h₀ : Module.Finite Γ(chartScheme A, ⊤) ((ModuleCat.restrictScalars g₀.appTop.hom).obj
      ((SheafOfModules.evaluation _ (op ⊤)).obj
        (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite T'))) :=
    moduleFinite_restrictScalars_appTop_sectionsTop g₀ _
  have h₁ : Module.Finite Γ(chartScheme A, ⊤) ((ModuleCat.restrictScalars g₀.appTop.hom).obj
      ((chartRestrictionSheaf B S hS X M T').val.obj (op ⊤))) :=
    moduleFinite_restrictScalars_of_iso g₀.appTop.hom
      ((SheafOfModules.evaluation _ (op ⊤)).mapIso
        ((restrictToChartIsoChartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite T').symm ≪≫
          restrictToChartIsoChartRestrictionSheaf B S hS X M T'))
  let R₂ := (smallEtaleRingSheaf B S hS Y.1 Y.2).obj.obj (op A)
  let Yt := (ModuleCat.restrictScalars g₀.appTop.hom).obj
    ((chartRestrictionSheaf B S hS X M T').val.obj (op ⊤))
  let : Module R₂ Yt := (inferInstance : Module Γ(chartScheme A, ⊤) Yt)
  have h₂ : Module.Finite R₂ Yt := h₁
  let ι := M.val.presheaf.mapIso (@asIso _ _ _ _ (chartOpensTopHom B S hS X T')
    (isIso_chartOpensTopHom B S hS X T')).op
  let φ : ((smallBaseChangeModulePushforward B S hS f hf).obj M).val.obj (op A) →ₗ[R₂] Yt :=
    { toFun := fun x => ULift.up (M.val.map (chartOpensTopHom B S hS X T').op x)
      map_add' := fun x y => ULift.ext _ _ (map_add _ x y)
      map_smul' := fun a x => ULift.ext _ _ (PresheafOfModules.map_smul _ _ _ _) }
  exact (Module.Finite.equiv (LinearEquiv.ofBijective φ
    (Equiv.ulift.symm.bijective.comp ι.addCommGroupIsoToAddEquiv.bijective)).symm :
    Module.Finite R₂ (((smallBaseChangeModulePushforward B S hS f hf).obj M).val.obj (op A)))

/-! ### Coherence of the direct image -/

/-- **The direct image of a coherent module along a proper representable morphism is coherent.**
Let `f : X ⟶ Y` be a representable proper morphism of algebraic spaces over `S`, with `Y` locally
Noetherian, and let `𝓕` be a coherent `𝒪_X`-module.  Then `f_*𝓕` is a coherent `𝒪_Y`-module.

It is quasi-coherent by Stacks 03M9, `f` being quasi-compact and quasi-separated, and its sections
over every affine étale chart of `Y` are finite by
`AlgebraicGeometry.Space.moduleFinite_modulePushforward_val_obj_of_isProper`, so the affine-chart
criterion of Stacks 07UB applies. -/
theorem isCoherent_modulePushforward_of_isProper (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (hfp : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) :
    IsCoherent B S hS Y.1 Y.2 ((modulePushforward B S hS f).obj M) :=
  have : M.IsQuasicoherentOnSite := hM.toIsQuasicoherentOnSite
  isCoherent_of_isQuasicoherentOnSite_of_forall_affine_moduleFinite B S hS Y.1 Y.2 hY _
    (isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f hfp.2.1.2
      (isQuasiSeparated_of_isSeparated B S hS hfp.1) M this)
    (fun A hA => moduleFinite_modulePushforward_val_obj_of_isProper B S hS f hf hfp hY M hM A hA)

/-! ### Coherence of the direct image along a finite morphism -/

/-- **Stacks 07UH, coherence of the direct image.**  Let `f : X ⟶ Y` be a finite morphism of
algebraic spaces over `S` with `Y` locally Noetherian, and let `𝓕` be a coherent `𝒪_X`-module.
Then `f_*𝓕` is a coherent `𝒪_Y`-module.

A finite morphism is affine, hence representable
(`AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`), and proper by Stacks 04NZ
(`AlgebraicGeometry.Space.isFinite_iff_isAffineHom_and_isProper`), so this is
`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isProper`.  The vanishing assertion of
Stacks 07UH is `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isFinite`. -/
@[stacks 07UH "coherence of the direct image"]
theorem isCoherent_modulePushforward_of_isFinite' (f : X ⟶ Y) (hf : IsFinite B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) :
    IsCoherent B S hS Y.1 Y.2 ((modulePushforward B S hS f).obj M) :=
  isCoherent_modulePushforward_of_isProper B S hS f
    (relativelyRepresentable_of_isAffineHom B S hS f hf.isAffineHom)
    ((isFinite_iff_isAffineHom_and_isProper B S hS X.2 Y.2 f.hom).1 hf).2 hY M hM

end AlgebraicGeometry.Space

end
