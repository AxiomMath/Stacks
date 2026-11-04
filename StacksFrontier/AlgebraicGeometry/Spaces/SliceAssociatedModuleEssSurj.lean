module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleAffineBaseChange

/-!
# What essential surjectivity of `(-)ᵃ` on the slice at a chart buys

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `X` be an
étale chart of `F` with underlying scheme `U`, and let `G` be an `𝒪_F`-module.  Descent,
Proposition 03DX(2) asserts that `M ↦ Mᵃ` is an equivalence from the quasi-coherent
`𝒪_U`-modules to the quasi-coherent modules on the small étale site of `U`; the slice of the
small étale site of `F` at `X` *is* that site
(`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSchemeSite`), and
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule` is the functor's value.

This file proves the implication that makes the *essential surjectivity* half of that
proposition usable in this tree: **if the restriction of `G` to the slice at `X` is isomorphic to
some `Mᵃ`, then the base change comparison**

`𝒪_F(V) ⊗_{𝒪_F(U')} G(U') ⟶ G(V)`

**of `AlgebraicGeometry.Space.sectionsBaseChange` is bijective for every morphism `V ⟶ U'` of
affine étale charts lying over `X`.**  That conclusion is the clause of
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` for the charts over `X`, which is the
hypothesis the chart-sections files of this tree carry throughout, so this is the bridge from
the essential image of `(-)ᵃ` to the hypothesis `h03DX`.

Essential surjectivity itself is **not** proved here; see the implementation notes for the
precise residue.

## Main results

* `Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_liftBaseChange_of_bijective` and
  `Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_liftBaseChange_of_linearEquiv`: a base
  change comparison that is computed on pure tensors is `LinearMap.liftBaseChange`, and
  bijectivity of such a comparison transfers along isomorphisms of its two sides.
* `bijective_liftBaseChange_of_bijective_extendScalars`, in the same namespace: **the
  translation between the two spellings of a base change comparison** — the
  `CategoryTheory.ModuleCat.extendScalars` one of
  `Stacks.Sites.affineAssociatedBaseChangeIso` and the `LinearMap.liftBaseChange` one of
  `AlgebraicGeometry.Space.sectionsBaseChange`.
* `Stacks.Sites.siteAssociatedModule_map_apply`: the restriction map of `Mᵃ` on a site of
  schemes is the pullback map on global sections of Tag 03DS.
* `Stacks.Sites.bijective_liftBaseChange_siteAssociatedModule`: **`Mᵃ` is cartesian between
  affine objects of a site of schemes**, in the `LinearMap.liftBaseChange` form.
* `Stacks.SheafOfModules.bijective_app`: an isomorphism of sheaves of modules is bijective on
  the sections over every object of the site.
* `AlgebraicGeometry.Space.SmallEtale.bijective_sectionsBaseChange_of_sliceAssociatedModule_iso`
  and its two corollaries
  `bijective_sectionsBaseChange_of_sliceAssociatedModule_iso_of_hom` and
  `bijective_sectionsBaseChange_of_exists_sliceAssociatedModule_iso`, in the same namespace:
  **the implication above**, in three shapes — with the isomorphism given, with the morphism of
  charts presented as a morphism of `F`-charts together with a morphism to `X`, and with the
  isomorphism's existence (that is, essential surjectivity at `X`) as the hypothesis.
* `AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj`: **essential
  surjectivity of `(-)ᵃ` on the slices at all affine charts gives
  `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` outright**, with no localization step —
  a morphism of affine charts `f : V ⟶ U` is already a morphism of the slice at `U`, so the
  hypothesis is used only at the larger chart.

## Implementation notes

Two spellings of one base change comparison have to be identified, and the identification is
where all the difficulty is.  `Stacks.Sites.affineAssociatedBaseChangeIso` is stated with
`CategoryTheory.ModuleCat.extendScalars`, whose `Module R S` instance is the `Module.compHom`
produced by `CategoryTheory.ModuleCat.restrictScalars`;
`AlgebraicGeometry.Space.sectionsBaseChange` is stated with `LinearMap.liftBaseChange`, whose
`Module R S` instance is the `Algebra.toModule` of `RingHom.toAlgebra`.  The two are
definitionally equal, and the implementation notes of
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleAffineBaseChange` record — correctly —
that the defeq check identifying them **exhausts the elaborator's default recursion depth at
these concrete sheaf-section types**, and so it does here: a `rw` across the boundary,
and even a term-mode `exact` of the normalisation lemma at the bare `TensorProduct` spelling,
both fail with `maximum recursion depth has been reached`.

The way through is not a bigger recursion depth, which is barred, but
`Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_liftBaseChange_of_bijective_extendScalars`
above: its statement mentions *both* spellings, so the defeq is discharged once, at abstract
types, where it is cheap; applying
the lemma afterwards is an instantiation and performs no further unfolding.  Two further
measurements in the same vein are recorded as separate lemmas, because
`rfl` for their conjunction exceeds the heartbeat budget while `rfl` for each exceeds nothing:
`Stacks.Sites.associatedPresheaf_map_apply` (which unfolds
`AlgebraicGeometry.quasiCoherentPresheafConstruction`) and
`Stacks.Sites.siteAssociatedModule_presheaf_map_apply` (which unfolds
`CategoryTheory.PresheafOfModules.ofPresheaf`).

The instance `Module (AlgebraicGeometry.Space.chartRing … Z.left) (Mᵃ(Z))` is not found by
instance search — the ring of the slice is `(… .over X).obj.obj (op Z)` and instance search does
not reduce it to the ring of the chart — and is supplied as the `CategoryTheory.ModuleCat`
object's own `isModule` field.  Writing it as `inferInstanceAs` instead makes the elaborator lift
the tactic `let` to an auxiliary definition and fail to compile it, `sliceAssociatedModule` being
noncomputable.

**Essential surjectivity.**  The hypothesis `hEss` of
`bijective_sectionsBaseChange_of_exists_sliceAssociatedModule_iso` is a theorem,
`AlgebraicGeometry.Space.exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/SliceAssociatedModuleEssSurjFromChart.lean`, with no
hypothesis.  The last step of the Stacks proof of 03DX(2) at an affine chart — that `M ↦ Mᵃ`
carries a cokernel of free modules to the cokernel — needs
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule`, which is built by hand, to be
identified with a `CategoryTheory.SheafOfModules.pullback`.  That identification is what
`SliceAssociatedModuleEssSurjFromChart.lean` supplies, and it is supplied without redoing the cokernel step: on the small étale site of the
chart's *scheme* the pullback description of `Gᵃ` is already identified with the sections
description by [Stacks, Tag 070S] part (2), which is proved unconditionally as
`AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso`; and on that site essential
surjectivity of the pullback description is proved unconditionally as
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`.  So the four-step
argument is not run on the slice at all — it is run once, on the scheme, where it already was,
and transported across the two comparisons of Tag 04M0, which are equivalences of module
categories.

Three of the four steps on the slice are nevertheless proved unconditionally, and are what a
direct run of the argument here would use:

* the presentation — `AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isAffine` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartSpaceGlobalPresentation.lean`, which is Stacks 03DX
  for the small étale ringed site of an algebraic space and gives
  `(G.over X).HasGlobalPresentation` for a quasi-coherent `G` at an affine chart, with no
  hypothesis.  **No localization argument is owed**: this is a global presentation *on the
  slice*, not on a covering of it;
* the free step — `AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_free` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SliceAssociatedModuleFree.lean`, whose sheaf-condition
  binder is discharged from Stacks 03DT in
  `AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_free_unconditional`;
* full faithfulness, Tag 0GN7 on this slice —
  `AlgebraicGeometry.Space.SmallEtale.bijective_associatedModuleMap_slice` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SliceAssociatedModuleFullness.lean`, likewise
  unconditional as
  `AlgebraicGeometry.Space.SmallEtale.bijective_associatedModuleMap_slice_unconditional`.

The universe remark that accompanied them still stands, and is a second reason not to run the
argument on the slice: `CategoryTheory.SheafOfModules.HasGlobalPresentation` presents at module
universe `u + 1` with index types in `Type (u + 1)` at this site, while
`CategoryTheory.SheafOfModules.free` exists only for `I : Type u`, so a direct run would have to
redo the free-module step at a free index universe.

What is *not* owed, contrary to what one might expect from the chart-sections files, is a
localization step on the cartesian side:
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj` gets
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` from essential surjectivity alone.

No `@[stacks]` attribute is claimed anywhere in this file.  Every statement about `G` carries the
essential image of `(-)ᵃ` as a hypothesis, and Descent, Proposition 03DX(2) is an equivalence of
categories; the convention of the sibling files
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsCokernel`,
`StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleCartesian` and
`StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModule` — no tag on a conditional statement
— is followed.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.SectionsBaseChange

variable {R S N N' : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module S N'] [Module R N']
    [IsScalarTower R S N']

/-- **A base change comparison that is computed on pure tensors is bijective when the computing
map is.**  If an additive map `e` out of `S ⊗_R N` sends `b ⊗ m` to `b • ρ m` then it *is* the
canonical comparison `LinearMap.liftBaseChange` of `ρ`, so bijectivity of one is bijectivity of
the other.

The hypotheses are pointwise on purpose: at the concrete sheaf-section types of this tree the
two sides of such a comparison arrive with different — definitionally equal, syntactically
distinct — scalar structures, and an equation between the bundled linear maps cannot be stated
without crossing that boundary. -/
theorem bijective_liftBaseChange_of_bijective (ρ : N →ₗ[R] N')
    (e : TensorProduct R S N → N')
    (hadd : ∀ z w, e (z + w) = e z + e w)
    (htmul : ∀ (b : S) (m : N), e (TensorProduct.tmul R b m) = b • ρ m)
    (hbij : Function.Bijective e) :
    Function.Bijective (ρ.liftBaseChange S) := by
  have h0 : e 0 = 0 := by simpa using hadd 0 0
  have key : ∀ z, ρ.liftBaseChange S z = e z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, h0]
    | tmul b m => rw [LinearMap.liftBaseChange_tmul, htmul]
    | add z w hz hw => rw [map_add, hz, hw, hadd]
  rwa [show (ρ.liftBaseChange S : TensorProduct R S N → N') = e from funext key]

variable {P P' : Type u} [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module S P']
    [Module R P'] [IsScalarTower R S P']

/-- **Bijectivity of a base change comparison transfers along isomorphisms of its two sides.**
Given `R`-linear `ρ : N ⟶ N'` and `σ : P ⟶ P'`, an `R`-linear isomorphism `α : N ≅ P` and an
`S`-linear isomorphism `β : N' ≅ P'` with `β ∘ ρ = σ ∘ α`, the comparison of `ρ` is bijective
as soon as the comparison of `σ` is. -/
theorem bijective_liftBaseChange_of_linearEquiv (ρ : N →ₗ[R] N') (σ : P →ₗ[R] P')
    (α : N ≃ₗ[R] P) (β : N' ≃ₗ[S] P') (hcomm : ∀ m, β (ρ m) = σ (α m))
    (h : Function.Bijective (σ.liftBaseChange S)) :
    Function.Bijective (ρ.liftBaseChange S) := by
  refine bijective_liftBaseChange_of_bijective ρ
    (fun z => β.symm (σ.liftBaseChange S (LinearMap.lTensor S (α : N →ₗ[R] P) z)))
    (fun z w => by simp only [map_add]) (fun b m => ?_)
    (β.symm.bijective.comp (h.comp (LinearEquiv.lTensor S α).bijective))
  simp only [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, LinearEquiv.coe_coe,
    map_smul]
  rw [← hcomm m, β.symm_apply_apply]

/-- **The extension-of-scalars form of a base change comparison is the
`LinearMap.liftBaseChange` form.**  If a morphism `e` out of `ModuleCat.extendScalars φ` of `N`
sends `1 ⊗ m` to `ρ m`, then bijectivity of `e` is bijectivity of the comparison
`S ⊗_R N ⟶ N'` of `ρ`, for the `R`-algebra structure on `S` and the `R`-module structure on
`N'` induced by `φ`.

This lemma exists in order to be *instantiated* at concrete sheaf-section types.  The two
descriptions of `S ⊗_R N` differ in the `Module R S` instance — `Module.compHom`, produced by
`CategoryTheory.ModuleCat.restrictScalars`, against `Algebra.toModule` of
`RingHom.toAlgebra` — and the defeq identifying them exhausts the elaborator's default
recursion depth at the section types of a sheaf on a site.  Proving the statement once at
abstract types and applying it afterwards replaces that check by an instantiation. -/
theorem bijective_liftBaseChange_of_bijective_extendScalars {R S N N' : Type u} [CommRing R]
    [CommRing S] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module S N'] (φ : R →+* S)
    (e : (ModuleCat.extendScalars φ).obj (ModuleCat.of R N) ⟶ ModuleCat.of S N')
    (hbij : Function.Bijective e) :
    letI := φ.toAlgebra
    letI := Module.compHom N' φ
    haveI : IsScalarTower R S N' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    ∀ ρ : N →ₗ[R] N', (∀ m : N, e ((1 : S) ⊗ₜ[R, φ] m) = ρ m) →
      Function.Bijective (ρ.liftBaseChange S) := by
  let _ := φ.toAlgebra
  let _ := Module.compHom N' φ
  have _ : IsScalarTower R S N' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  intro ρ hρ
  refine bijective_liftBaseChange_of_bijective (S := S) ρ (fun z => e z)
    (fun z w => map_add _ z w) (fun b m => ?_) hbij
  have hb : TensorProduct.tmul R b m = b • TensorProduct.tmul R (1 : S) m := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hb, show e (b • TensorProduct.tmul R (1 : S) m) = _ from
    map_smul (ConcreteCategory.hom e) b _]
  exact congrArg (fun x => b • x) (hρ m)

end Stacks.AlgebraicGeometry.SectionsBaseChange

open Stacks.AlgebraicGeometry.SectionsBaseChange

namespace Stacks.Sites

open _root_.AlgebraicGeometry

variable {T : Scheme.{u}} (M : T.Modules) [M.IsQuasicoherent]
    {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over T)

/-- The restriction map of the associated presheaf of Tag 03DU is the pullback map on global
sections of Tag 03DS.  Stated and proved at an abstract site, so that the unfolding of
`AlgebraicGeometry.quasiCoherentPresheafFunctor` it performs happens once. -/
theorem associatedPresheaf_map_apply {c₁ c₂ : C} (f : c₂ ⟶ c₁)
    (a : (associatedPresheaf T M toOver).obj (op c₁)) :
    (associatedPresheaf T M toOver).map f.op a =
      AlgebraicGeometry.pullbackSectionsMap M (toOver.map f) a := rfl

variable (J : GrothendieckTopology C)
    (hR : Presheaf.IsSheaf J (structurePresheaf T toOver))
    (hM : Presheaf.IsSheaf J (associatedPresheaf T M toOver))

/-- The underlying abelian presheaf of the sheaf of modules `Fᵃ` has the restriction maps of
the associated presheaf.  Stated at an abstract site for the same reason as
`Stacks.Sites.associatedPresheaf_map_apply`. -/
theorem siteAssociatedModule_presheaf_map_apply {c₁ c₂ : C} (f : c₂ ⟶ c₁)
    (a : (siteAssociatedModule T M toOver J hR hM).val.obj (op c₁)) :
    ((siteAssociatedModule T M toOver J hR hM).val.presheaf.map f.op).hom a =
      (associatedPresheaf T M toOver).map f.op a := rfl

/-- **The restriction map of `Fᵃ` is the pullback map on sections.**  This is the composite of
`Stacks.Sites.siteAssociatedModule_presheaf_map_apply`,
`Stacks.Sites.associatedPresheaf_map_apply` and
`CategoryTheory.PresheafOfModules.presheaf_map_apply_coe`; stating it directly as `rfl` exceeds
the elaborator's heartbeat budget, because it unfolds
`CategoryTheory.PresheafOfModules.ofPresheaf` and
`AlgebraicGeometry.quasiCoherentPresheafConstruction` at once. -/
theorem siteAssociatedModule_map_apply {c₁ c₂ : C} (f : c₂ ⟶ c₁)
    (a : (siteAssociatedModule T M toOver J hR hM).val.obj (op c₁)) :
    (siteAssociatedModule T M toOver J hR hM).val.map f.op a =
      AlgebraicGeometry.pullbackSectionsMap M (toOver.map f) a :=
  (PresheafOfModules.presheaf_map_apply_coe _ f.op a).symm.trans
    ((siteAssociatedModule_presheaf_map_apply M toOver J hR hM f a).trans
      (associatedPresheaf_map_apply M toOver f a))

/-- **The affine base change comparison of `Fᵃ` in `LinearMap.liftBaseChange` form.**  For a
morphism `g : Z₂ ⟶ Z₁` of schemes over `T` whose two underlying schemes are affine and `M` a
quasi-coherent `𝒪_T`-module, the comparison

`Γ(Z₂.left, 𝒪) ⊗_{Γ(Z₁.left, 𝒪)} Γ(Z₁.hom⁺ M, ⊤) ⟶ Γ(Z₂.hom⁺ M, ⊤)`

extending the restriction map of `Mᵃ` is bijective.

The ring map, the scalar structures and the comparison are all parameters pinned by equations,
in the shape a caller that has just built them can supply; that is what lets this be applied on
a site whose rings of functions are reached through a different instance path.  The content is
`Stacks.Sites.bijective_affineAssociatedBaseChangeIso_hom`, converted from the
`CategoryTheory.ModuleCat.extendScalars` form by
`Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_liftBaseChange_of_bijective_extendScalars`.
-/
theorem bijective_liftBaseChange_siteAssociatedModule {Z₁ Z₂ : Over T} (g : Z₂ ⟶ Z₁)
    [IsAffine Z₁.left] [IsAffine Z₂.left]
    (hle : (⊤ : Z₂.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : Z₁.left.Opens))
    (φ : Γ(Z₁.left, ⊤) →+* Γ(Z₂.left, ⊤)) (hφ : φ = (g.left.appLE ⊤ ⊤ hle).hom) :
    letI := φ.toAlgebra
    letI := Module.compHom Γ((Scheme.Modules.pullback Z₂.hom).obj M, ⊤) φ
    haveI : IsScalarTower Γ(Z₁.left, ⊤) Γ(Z₂.left, ⊤)
        Γ((Scheme.Modules.pullback Z₂.hom).obj M, ⊤) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    ∀ ρ : Γ((Scheme.Modules.pullback Z₁.hom).obj M, ⊤) →ₗ[Γ(Z₁.left, ⊤)]
        Γ((Scheme.Modules.pullback Z₂.hom).obj M, ⊤),
      (∀ a, ρ a = _root_.AlgebraicGeometry.pullbackSectionsMap M g a) →
        Function.Bijective (ρ.liftBaseChange Γ(Z₂.left, ⊤)) := by
  subst hφ
  intro ρ hρ
  exact bijective_liftBaseChange_of_bijective_extendScalars _
    (affineAssociatedBaseChangeIso M g hle).hom
    (bijective_affineAssociatedBaseChangeIso_hom M g hle)
    ρ (fun m => (affineAssociatedBaseChangeIso_hom_one_tmul M g hle m).trans (hρ m).symm)

end Stacks.Sites

namespace Stacks.SheafOfModules

universe v' u' r m

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {A A' : _root_.SheafOfModules.{m} R}

/-- Two mutually inverse morphisms of sheaves of modules are mutually inverse on the sections
over every object of the site. -/
theorem app_comp_eq_id (φ : A ⟶ A') (ψ : A' ⟶ A) (h : φ ≫ ψ = 𝟙 A) (c : Cᵒᵖ) :
    (ψ.val.app c).hom.comp (φ.val.app c).hom = LinearMap.id := by
  have h' : (φ.val.app c) ≫ (ψ.val.app c) = 𝟙 _ := by
    rw [← PresheafOfModules.comp_app, ← _root_.SheafOfModules.comp_val, h]
    rfl
  exact congrArg ModuleCat.Hom.hom h'

/-- An isomorphism of sheaves of modules is bijective on the sections over every object of the
site. -/
theorem bijective_app (φ : A ⟶ A') (ψ : A' ⟶ A) (h₁ : φ ≫ ψ = 𝟙 A) (h₂ : ψ ≫ φ = 𝟙 A')
    (c : Cᵒᵖ) : Function.Bijective (φ.val.app c) :=
  Function.bijective_iff_has_inverse.2
    ⟨ψ.val.app c, fun x => congrArg (fun l => l x) (app_comp_eq_id φ ψ h₁ c),
      fun x => congrArg (fun l => l x) (app_comp_eq_id ψ φ h₂ c)⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space.SmallEtale

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (X : SmallEtale B S hS F)

/-- **A module on an algebraic space which is `Mᵃ` on the slice at a chart is cartesian between
the affine charts over that chart.**

Let `G` be an `𝒪_F`-module, `X` an étale chart of `F`, and suppose the restriction of `G` to the
slice at `X` is isomorphic to the module `Mᵃ` of Tag 03DU of a quasi-coherent module `M` on the
chart's scheme.  Then for every morphism `f : Z₂ ⟶ Z₁` of charts over `X` whose two underlying
schemes are affine, the base change comparison

`𝒪_F(Z₂) ⊗_{𝒪_F(Z₁)} G(Z₁) ⟶ G(Z₂)`

of `AlgebraicGeometry.Space.sectionsBaseChange` is bijective.

This is what makes essential surjectivity of `(-)ᵃ` on the slice at an affine chart useful: the
conclusion is exactly the clause of `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` for the
charts lying over `X`, which is the hypothesis the chart-sections files of this tree carry.  The
content is the affine base change isomorphism of `Mᵃ`
(`Stacks.Sites.bijective_liftBaseChange_siteAssociatedModule`) transported along the two
components of the isomorphism. -/
theorem bijective_sectionsBaseChange_of_sliceAssociatedModule_iso
    (G : Modules.{u, u} B S hS F hF) (M : (chartScheme X).Modules)
    [M.IsQuasicoherent]
    (hM : Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) M (sliceToOver B S hS F X)))
    (e : sliceModule B S hS F hF X G ≅ sliceAssociatedModule B S hS F hF X M hM)
    {Z₁ Z₂ : Over X} (f : Z₂ ⟶ Z₁)
    (h₁ : IsAffine (chartScheme Z₁.left))
    (h₂ : IsAffine (chartScheme Z₂.left)) :
    Function.Bijective (sectionsBaseChange G f.left) := by
  have i₁ : IsAffine ((sliceToOver B S hS F X).obj Z₁).left := h₁
  have i₂ : IsAffine ((sliceToOver B S hS F X).obj Z₂).left := h₂
  let _ := chartAlgebra (hF := hF) f.left
  let _ := chartSectionsModule G f.left
  have _ := chartSections_isScalarTower G f.left
  let _ : Module (chartRing B S hS F hF Z₁.left)
      ((sliceAssociatedModule B S hS F hF X M hM).val.obj (op Z₁)) :=
    ((sliceAssociatedModule B S hS F hF X M hM).val.obj (op Z₁)).isModule
  let _ : Module (chartRing B S hS F hF Z₂.left)
      ((sliceAssociatedModule B S hS F hF X M hM).val.obj (op Z₂)) :=
    ((sliceAssociatedModule B S hS F hF X M hM).val.obj (op Z₂)).isModule
  let _ : Module (chartRing B S hS F hF Z₁.left)
      ((sliceAssociatedModule B S hS F hF X M hM).val.obj (op Z₂)) :=
    Module.compHom _ (chartRestrict (hF := hF) f.left)
  have _ : IsScalarTower (chartRing B S hS F hF Z₁.left) (chartRing B S hS F hF Z₂.left)
      ((sliceAssociatedModule B S hS F hF X M hM).val.obj (op Z₂)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let σ : ((sliceAssociatedModule B S hS F hF X M hM).val.obj (op Z₁) : Type u) →ₗ[
      chartRing B S hS F hF Z₁.left]
      ((sliceAssociatedModule B S hS F hF X M hM).val.obj (op Z₂) : Type u) :=
    ((sliceAssociatedModule B S hS F hF X M hM).val.map f.op).hom
  have hσ : Function.Bijective (σ.liftBaseChange (chartRing B S hS F hF Z₂.left)) :=
    Stacks.Sites.bijective_liftBaseChange_siteAssociatedModule M
      ((sliceToOver B S hS F X).map f) (by simp) (chartRestrict (hF := hF) f.left)
      (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_eq_app _).symm) σ
      (fun a => Stacks.Sites.siteAssociatedModule_map_apply M (sliceToOver B S hS F X)
        ((topology B S hS F).over X) (isSheaf_sliceStructurePresheaf B S hS F hF X) hM f a)
  have hb := Stacks.SheafOfModules.bijective_app e.hom e.inv e.hom_inv_id e.inv_hom_id
  exact bijective_liftBaseChange_of_linearEquiv (chartRestrictLinear G f.left) σ
    (.ofBijective _ (hb (op Z₁))) (.ofBijective _ (hb (op Z₂)))
    (fun m => PresheafOfModules.naturality_apply e.hom.val f.op m) hσ

/-- **The same conclusion for a morphism of charts equipped with a morphism to `X`.**  A
morphism `f : V ⟶ U` of affine étale charts together with a morphism `p : U ⟶ X` of charts is a
morphism of the slice at `X`, so the base change comparison of `G` over `f` is bijective as soon
as the restriction of `G` to the slice at `X` is an `Mᵃ`.

This is the shape in which `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` is stated, with
the one extra datum — the morphism to `X` — that restricts it to the charts over `X`. -/
theorem bijective_sectionsBaseChange_of_sliceAssociatedModule_iso_of_hom
    (G : Modules.{u, u} B S hS F hF) (M : (chartScheme X).Modules)
    [M.IsQuasicoherent]
    (hM : Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) M (sliceToOver B S hS F X)))
    (e : sliceModule B S hS F hF X G ≅ sliceAssociatedModule B S hS F hF X M hM)
    {U V : SmallEtale B S hS F} (f : V ⟶ U) (p : U ⟶ X)
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) :
    Function.Bijective (sectionsBaseChange G f) :=
  bijective_sectionsBaseChange_of_sliceAssociatedModule_iso B S hS F hF X G M hM e
    (Z₁ := Over.mk p) (Z₂ := Over.mk (f ≫ p)) (Over.homMk f rfl) hU hV

/-- **Essential surjectivity of `(-)ᵃ` on the slice at a chart gives the base change criterion
over that chart.**

Suppose that the restriction of `G` to the slice of the small étale site of `F` at the chart `X`
is *isomorphic to some* `Mᵃ` — that is, suppose `G|_X` is in the essential image of the functor
`M ↦ Mᵃ` of Tag 03DU on the slice.  Then the base change comparison of `G` is bijective over
every morphism of affine charts lying over `X`.

The hypothesis is the conclusion of essential surjectivity in Descent, Proposition 03DX(2) at
the chart `X`, in the spelling the slice construction of
`StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModule` produces.  It is not proved in this
tree; see the implementation notes for what is owed.  No `@[stacks]` attribute is claimed: this
is one implication of Tag 03DX(2) and carries its essential surjectivity as a hypothesis. -/
theorem bijective_sectionsBaseChange_of_exists_sliceAssociatedModule_iso
    (G : Modules.{u, u} B S hS F hF)
    (hEss : ∃ (M : (chartScheme X).Modules) (_ : M.IsQuasicoherent)
      (hM : Presheaf.IsSheaf ((topology B S hS F).over X)
        (Stacks.Sites.associatedPresheaf (chartScheme X) M (sliceToOver B S hS F X))),
      Nonempty (sliceModule B S hS F hF X G ≅ sliceAssociatedModule B S hS F hF X M hM))
    {U V : SmallEtale B S hS F} (f : V ⟶ U) (p : U ⟶ X)
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) :
    Function.Bijective (sectionsBaseChange G f) := by
  obtain ⟨M, _, hM, ⟨e⟩⟩ := hEss
  exact bijective_sectionsBaseChange_of_sliceAssociatedModule_iso_of_hom B S hS F hF X G M hM e
    f p hU hV

/-- **Essential surjectivity of `(-)ᵃ` at every affine chart gives
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` outright.**

For `f : V ⟶ U` a morphism of affine étale charts, `f` *is* a morphism of the slice at `U`, so
the hypothesis is needed only at the larger chart and no passage from a covering to the chart
itself intervenes: the localization step that the chart-sections files expect is not used.

What this does **not** do is derive the hypothesis from quasi-coherence.
`CategoryTheory.SheafOfModules.IsQuasicoherentOnSite` gives a global presentation only on the
members of *some* covering of each object, not over the object itself, so getting `hEss` from
it is a separate statement — and that is where a localization argument is needed.  So this
theorem reduces the forward implication of Descent, Proposition 03DX(2) for the small étale site
of `F`, in the spelling

`∀ G, G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G`

that this tree carries as `h03DX`, to essential surjectivity of `(-)ᵃ` on the slices at affine
charts.  The reverse implication is not touched. -/
theorem isCartesianOnAffineCharts_of_essSurj (G : Modules.{u, u} B S hS F hF)
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∃ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent)
        (hM : Presheaf.IsSheaf ((topology B S hS F).over Y)
          (Stacks.Sites.associatedPresheaf (chartScheme Y) M
            (sliceToOver B S hS F Y))),
        Nonempty (sliceModule B S hS F hF Y G ≅ sliceAssociatedModule B S hS F hF Y M hM)) :
    IsCartesianOnAffineCharts G := fun U _V hU hV f =>
  bijective_sectionsBaseChange_of_exists_sliceAssociatedModule_iso B S hS F hF U G
    (hEss U hU) f (𝟙 U) hU hV

end AlgebraicGeometry.Space.SmallEtale

end
