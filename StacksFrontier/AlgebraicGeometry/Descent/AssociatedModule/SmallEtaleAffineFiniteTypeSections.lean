module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineFlatRefinement

/-!
# The sections of a quasi-coherent module of finite type over an affine étale object

Let `S` be a scheme contained in a big étale site and let `𝓖` be a sheaf of modules on the small
étale site of `S` which is quasi-coherent and of finite type.  This file proves that the sections
of `𝓖` over an *affine* object of that site form a finite module over the ring of regular
functions there.

## Main definitions

* `AlgebraicGeometry.SmallEtale.affineChartModule` and
  `AlgebraicGeometry.SmallEtale.affineChartPresheaf`: the restriction of a sheaf of modules on
  the small étale site to the small affine étale site, as a sheaf of modules over the restricted
  structure sheaf and as a presheaf of modules over the chart rings.

## Main results

* `Stacks.SheafOfModules.generates_pushforward`: a finite family of sections generating a sheaf of
  modules on a site generates its restriction to a cocontinuous subsite.
* `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_affineChartModule`: a
  quasi-coherent sheaf of modules on the small étale site is cartesian over every arrow of the
  small affine étale site, for the chart rings.
* `AlgebraicGeometry.SmallEtale.module_finite_sections_affineChartModule_of_isFiniteTypeOnSite`:
  **the sections over an affine object of the small étale site of a quasi-coherent module of
  finite type form a finite module over the ring of regular functions there.**

## Implementation notes

The restriction of the module is spelled twice.  `affineChartModule` is the sheaf of modules over
the pushforward of the structure sheaf along the inclusion, which is what
`Stacks.SheafOfModules.isQuasicoherentOnSite_restriction` and
`Stacks.SheafOfModules.generates_pushforward` produce; `affineChartPresheaf` is the same object
ascribed the type `PresheafOfModules (affineChartRings ⋙ forget₂ CommRingCat RingCat)`, which is
the type whose `Module` instances type class inference finds when the ring of scalars is written
as `affineChartRings`.  The two are definitionally equal and the ascription is the whole content
of the second.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m u' v'

namespace Stacks.SheafOfModules

/-- **A finite generating family transports to a cocontinuous subsite.**  If the sections
`s` over `F U` generate a sheaf of modules `M` on the ambient site, then they generate the
restriction of `M` along `F` on the subsite. -/
theorem generates_pushforward {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} (F : C ⥤ D)
    [F.IsContinuous J K] [F.IsCocontinuous J K]
    {R : Sheaf K RingCat.{w}} (M : SheafOfModules.{m} R) {U : C} {n : ℕ}
    (s : Fin n → M.val.obj (op (F.obj U)))
    (hs : PresheafOfModules.Generates K M.val s) :
    PresheafOfModules.Generates J
      ((_root_.SheafOfModules.pushforward.{m} (F := F) (J := J) (K := K)
        (S := (F.sheafPushforwardContinuous RingCat.{w} J K).obj R) (𝟙 _)).obj M).val s := by
  intro V f t
  obtain ⟨T, hT, hc⟩ := hs (F.obj V) (F.map f) t
  refine ⟨Sieve.functorPullback F T, Functor.IsCocontinuous.cover_lift (G := F) hT, ?_⟩
  intro W g hg
  obtain ⟨a, ha⟩ := hc (F.obj W) (F.map g) hg
  refine ⟨fun i => a i, ?_⟩
  show ∑ i, a i • (M.val.restrictₛₗ (F.map (g ≫ f)).op) (s i) =
    (M.val.restrictₛₗ (F.map g).op) t
  rw [F.map_comp]
  exact ha

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

open Stacks.PresheafOfModules

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The small affine étale site as a dense cocontinuous subsite -/

/-- The inclusion of the small affine étale site of `S` into its small étale site exhibits the
first as a dense subsite of the second. -/
theorem smallAffineEtale_inclusion_isDenseSubsite :
    (SmallAffineEtale.inclusion B S hS).IsDenseSubsite
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
  (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2

/-- The inclusion of the small affine étale site of `S` into its small étale site is
cocontinuous. -/
theorem smallAffineEtale_inclusion_isCocontinuous :
    (SmallAffineEtale.inclusion B S hS).IsCocontinuous
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
  (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).1

attribute [local instance] smallAffineEtale_inclusion_isDenseSubsite
  smallAffineEtale_inclusion_isCocontinuous

/-- The inclusion of the small affine étale site is continuous on every slice. -/
instance smallAffineEtale_overPost_isContinuous (X : SmallAffineEtale B S hS) :
    (Over.post (X := X) (SmallAffineEtale.inclusion B S hS)).IsContinuous
      ((SmallAffineEtale.topology B S hS).over X)
      ((topology B S hS).over ((SmallAffineEtale.inclusion B S hS).obj X)) := by
  have _ := Stacks.Sites.overPost_isDenseSubsite
    (J := SmallAffineEtale.topology B S hS) (K := topology B S hS)
    (SmallAffineEtale.inclusion B S hS) X
  infer_instance

/-! ### The restriction of a module to the affine subsite -/

/-- The restriction to the small affine étale site of a sheaf of modules on the small étale site
of `S`, over the restriction of the structure sheaf. -/
noncomputable abbrev affineChartModule (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    SheafOfModules.{u}
      (((SmallAffineEtale.inclusion B S hS).sheafPushforwardContinuous RingCat.{u}
        (SmallAffineEtale.topology B S hS) (topology B S hS)).obj (structureSheaf B S hS)) :=
  (_root_.SheafOfModules.pushforward.{u} (𝟙 _)).obj G

/-- `AlgebraicGeometry.SmallEtale.affineChartModule`, read as a presheaf of modules over the
chart rings `AlgebraicGeometry.SmallEtale.affineChartRings`.  The two types are definitionally
equal. -/
noncomputable abbrev affineChartPresheaf (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    PresheafOfModules.{u} (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat) :=
  (affineChartModule B S hS G).val

/-! ### Descent, Proposition 03DX (2) on the affine subsite -/

/-- **A quasi-coherent sheaf of modules on the small étale site of a scheme is cartesian over
every arrow of the small affine étale site**, for the chart rings. -/
@[stacks 03DX "quasi-coherent implies cartesian over the small affine étale site of a scheme"]
theorem bijective_restrictionBaseChange_affineChartModule
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    {X Y : (SmallAffineEtale B S hS)ᵒᵖ} (a : X ⟶ Y) :
    Function.Bijective (restrictionBaseChange.{u + 1, u, u, u}
      (R := affineChartRings B S hS) (affineChartPresheaf B S hS G) a) := by
  have h₁ := Stacks.SheafOfModules.isQuasicoherentOnSite_restriction
    (J := topology B S hS) (K := SmallAffineEtale.topology B S hS)
    (SmallAffineEtale.inclusion B S hS) (structureSheaf B S hS) G hG
  have h₂ := _root_.SheafOfModules.isQuasicoherentOnSite_uliftForPresentation h₁
  have h₃ := isIso_restrictionBaseChange_affineChart_of_isQuasicoherentOnSite.{u, u}
    B S hS _ _ h₂ a.unop
  exact bijective_restrictionBaseChange_of_uliftForPresentation
    (affineChartRings B S hS) _ _ _ h₃

/-! ### Finiteness of the sections over an affine object -/

/-- **The sections of a quasi-coherent sheaf of modules of finite type over an affine object of
the small étale site of `S` form a finite module over the ring of regular functions there.** -/
theorem module_finite_sections_affineChartModule_of_isFiniteTypeOnSite
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    (hft : _root_.SheafOfModules.IsFiniteTypeOnSite G) (W : SmallAffineEtale B S hS) :
    Module.Finite ((affineChartRings B S hS).obj (op W))
      ((affineChartPresheaf B S hS G).obj (op W)) := by
  classical
  obtain ⟨I, V, f, hcov, hgg⟩ :=
    hft.locally_finitelyGenerated ((SmallAffineEtale.inclusion B S hS).obj W)
  set T : Sieve W :=
    Sieve.functorPullback (SmallAffineEtale.inclusion B S hS) (Sieve.ofArrows V f) with hTdef
  have hTmem : T ∈ SmallAffineEtale.topology B S hS W :=
    Functor.IsCocontinuous.cover_lift (G := SmallAffineEtale.inclusion B S hS) hcov
  refine module_finite_sections_affineChart_of_locally_generates.{u, u} B S hS
    (affineChartPresheaf B S hS G)
    (fun a => bijective_restrictionBaseChange_affineChartModule B S hS G hG a)
    (I := Σ X : SmallAffineEtale B S hS, {g : X ⟶ W // T.arrows g})
    (V := fun x => x.1) (f := fun x => x.2.1) ?_ ?_
  · refine (SmallAffineEtale.topology B S hS).superset_covering ?_ hTmem
    intro Z g hg
    exact Sieve.ofArrows_mk _ _ (⟨Z, g, hg⟩ :
      Σ X : SmallAffineEtale B S hS, {g : X ⟶ W // T.arrows g})
  · rintro ⟨Z, g, hg⟩
    obtain ⟨j, b, hb⟩ := (Sieve.mem_ofArrows_iff V f _).1 hg
    obtain ⟨k, σ, hσ⟩ :=
      Stacks.SheafOfModules.exists_generates_of_hasFiniteGlobalGenerators_over G (V j) (hgg j)
    refine ⟨k, fun l => G.val.restrictₛₗ b.op (σ l), ?_⟩
    exact Stacks.SheafOfModules.generates_pushforward
      (SmallAffineEtale.inclusion B S hS) G _
      (Stacks.SheafOfModules.generates_restrict b σ hσ)

end AlgebraicGeometry.SmallEtale

end
