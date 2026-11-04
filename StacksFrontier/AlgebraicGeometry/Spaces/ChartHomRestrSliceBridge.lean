module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartAlphaBaseCase

/-!
# The components of a relocalization of a morphism on the slice at a chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `ℐ ⊆ 𝒪_X` be a sheaf
of ideals which is cartesian on affine charts, let `U = X ∖ V(ℐ)`, let `𝒢` be coherent and `ℱ`
quasi-coherent and let `θ : 𝒢|_U ⟶ ℱ|_U`.  The one-chart gluing
`AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod` and the relocalization statements
of `StacksFrontier/AlgebraicGeometry/Spaces/ChartPushBaseChange.lean` are stated for *presheaves* of
modules over the structure presheaf, with the chart transport appearing as
`AlgebraicGeometry.Space.homRestr`; the chart transport
`AlgebraicGeometry.Space.chartAlphaSheaf` of `θ` and its component determination
`AlgebraicGeometry.Space.chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict` are stated for
morphisms of *sheaves* of modules on the slice of the small étale site at the chart.  **This file
joins the two spellings**, and draws the consequence the descent from the chart needs.

Both halves of the join are definitional.  `SheafOfModules.over` and the `restrFun` of
[Stacks, Tag 03EM] agree on underlying presheaves of modules, so the underlying morphism of a
morphism of the slice restrictions *is* a morphism of the `restrFun` restrictions with no
transport; and `AlgebraicGeometry.Space.homRestr` is evaluable with no base change, its component
over an object `Z` of the slice at the smaller chart being the component of the morphism itself
over the image of `Z` in the slice at the larger one.  What is new here is only that the two are
put side by side: nothing in the tree evaluates a relocalization of a morphism that was produced
as a morphism of sheaves of modules.

## Main results

* `Stacks.PresheafOfModules.homRestr_app_apply`: **the component of a relocalization, on a
  section**, by `rfl` — over an object `Z` of the slice at the smaller index it is the component
  of the morphism itself over `Over.mk (Z.hom ≫ f)`.  This is
  `Stacks.PresheafOfModules.toPresheaf_map_homRestr_app` read at the module component rather than
  at the underlying abelian presheaf, which is where a consumer with a section in hand needs it.
* `Stacks.PresheafOfModules.homRestr_homRestr_app_apply`: the same for an iterated
  relocalization, which is the shape the compatibility condition of
  `AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod_openChart` presents.
* `Stacks.PresheafOfModules.homRestr_eq_of_forall_app_apply`: **two relocalizations of one
  morphism along two indices agree as soon as all of their components do.**  Stated generically,
  where the ring of the component is reached without unfolding any chart datum.
* `AlgebraicGeometry.Space.val_app_homRestr_apply`: **the join.**  The component on a section of
  the relocalization along `p : A' ⟶ A` of the underlying presheaf morphism of
  `α : M|_A ⟶ N|_A` is the component of `α` over `Over.mk (Z.hom ≫ p)`.
* `AlgebraicGeometry.Space.homRestr_chartAlphaSheaf_eq_of_pc_eq`: **the two relocalizations of the
  chart transport of `θ` along any two morphisms out of a chart lying over `U` agree.**  Every
  component of either is the transport of `θ` at one and the same chart of `U`, namely the source
  of the slice object, which lies over `U` because the chart it sits over does.
* `AlgebraicGeometry.Space.homRestr_openChartInclusion_homRestr_prod_eq`: that statement at the
  chart cut out by the complement of the support of the chartwise sheaf of ideals in the kernel
  pair `A ⨯ A`, which is where the descent from the chart consumes it: the two relocalizations of
  the chart transport along the two projections of the kernel pair agree *over that open*.

## Implementation notes

**The ext principle is stated generically and applied first-order.**  At the chart the ring over
which a component of a relocalization is linear is `(ORestr … A').obj Z`, and deciding that it is
the ring of the component of `α` over `Over.mk (Z.hom ≫ p)` costs the heartbeat budget if
`CategoryTheory.ModuleCat.hom_ext` is asked to infer it from a goal built out of chart data:
the chart-level ext times out at `whnf`, the generic one is instant and its
instantiation at the chart is first-order.  `homRestr_eq_of_forall_app_apply` therefore carries
the two indices and the morphism and nothing of the chart.

**The agreement is not over the kernel pair but over an open of it.**  Instantiating
`AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod_openChart` with the complement of
the support as the covering family of `chartScheme (A ⨯ A)` is not possible:
`AlgebraicGeometry.Space.support_compl_idealSheafDataOfChart` is an *equality*, so that family
covers `chartScheme (A ⨯ A)` only when `ℐ = 𝒪_X`.  What is available, and what
`AlgebraicGeometry.Space.homRestr_openChartInclusion_homRestr_prod_eq` states, is the agreement
after relocalizing to the chart which the complement of the support cuts out — off the support
the component determination applies, and on the support nothing is known about the components of
the chart transport.  Raising the exponent of the ideal is what turns that into agreement over
the whole kernel pair, and it is not done here.

**No declaration here carries a `stacks` tag.**  This is an input to [Stacks, Tag 07UM], not an
assertion of it: the descent from the chart is not proved here, and the surjectivity clause of
Tag 07UM is therefore still unavailable.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.PresheafOfModules

universe v₁ u₁ t₁

variable {C : Type u₁} [Category.{v₁} C] (O : Cᵒᵖ ⥤ CommRingCat)
  (M N : _root_.PresheafOfModules.{t₁} (Oforget O))

/-- **The component of a relocalization, on a section.**  Over an object `Z` of the slice at the
smaller index the relocalization of `α` along `f` is `α` over `Over.mk (Z.hom ≫ f)`, the image of
`Z` in the slice at the larger index.

This holds by `rfl`: the restriction of a presheaf of modules to a slice has, over an object of
that slice, the sections of the module over its source, so no base change intervenes.  It is
`Stacks.PresheafOfModules.toPresheaf_map_homRestr_app` read at the module component. -/
theorem homRestr_app_apply {V U : C} (f : V ⟶ U)
    (α : (restrFun O U).obj M ⟶ (restrFun O U).obj N) (Z : (Over V)ᵒᵖ)
    (x : ((restrFun O V).obj M).obj Z) :
    ((homRestr O M N f α).app Z).hom x =
      ((α.app (op (Over.mk (Z.unop.hom ≫ f)))).hom x) := rfl

/-- **The component of an iterated relocalization, on a section.**  The relocalization along
`r : Q ⟶ A'` of the relocalization of `α` along `k : A' ⟶ A` is, over `Z`, the component of `α`
over `Over.mk ((Z.hom ≫ r) ≫ k)`. -/
theorem homRestr_homRestr_app_apply {A A' Q : C} (k : A' ⟶ A) (r : Q ⟶ A')
    (α : (restrFun O A).obj M ⟶ (restrFun O A).obj N) (Z : (Over Q)ᵒᵖ)
    (x : ((restrFun O Q).obj M).obj Z) :
    ((homRestr O M N r (homRestr O M N k α)).app Z).hom x =
      ((α.app (op (Over.mk ((Z.unop.hom ≫ r) ≫ k)))).hom x) := rfl

/-- **Two relocalizations of one morphism along two indices agree as soon as all of their
components do.**

The hypothesis is stated with the components of `α` itself rather than with the components of the
two relocalizations, which is what makes the instantiation at a chart first-order: the ring over
which a component is linear is reached here without unfolding any chart datum. -/
theorem homRestr_eq_of_forall_app_apply {V U : C} (p q : V ⟶ U)
    (α : (restrFun O U).obj M ⟶ (restrFun O U).obj N)
    (h : ∀ (Z : (Over V)ᵒᵖ) (x : ((restrFun O V).obj M).obj Z),
      ((α.app (op (Over.mk (Z.unop.hom ≫ p)))).hom x) =
        ((α.app (op (Over.mk (Z.unop.hom ≫ q)))).hom x)) :
    homRestr O M N p α = homRestr O M N q α :=
  _root_.PresheafOfModules.hom_ext fun Z =>
    ModuleCat.hom_ext (LinearMap.ext fun x => h Z x)

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The join of the slice spelling and the relocalization spelling -/

/-- **The join.**  A morphism `α : M|_A ⟶ N|_A` of the restrictions to the slice of the small
étale site of `X` at a chart has an underlying morphism of the `restrFun` restrictions of the
underlying presheaves of modules, with no transport; the component on a section of its
relocalization along `p : A' ⟶ A` is the component of `α` over `Over.mk (Z.hom ≫ p)`.

Both halves hold by `rfl`, and this is the only statement in the tree that puts them side by
side. -/
theorem val_app_homRestr_apply (M N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    {A A' : SmallEtale B S hS X.1} (p : A' ⟶ A) (α : M.over A ⟶ N.over A)
    (Z : (Over A')ᵒᵖ)
    (x : ((restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) A').obj M.val).obj Z) :
    ((homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) M.val N.val p α.val).app Z).hom x =
      (α.val.app (op (Over.mk (Z.unop.hom ≫ p)))).hom x :=
  Stacks.PresheafOfModules.homRestr_app_apply (smallEtaleStructurePresheaf B S hS X.1 X.2)
    M.val N.val p α.val Z x

/-! ### The two relocalizations of the chart transport of `θ` -/

section ChartAlpha

variable (I : IdealSheaves B S hS X.1 X.2)
    (hIc : IsCartesianOnAffineCharts I.toSheafOfModules)
    (G F : Modules.{u, u} B S hS X.1 X.2)
    (θ : (restrictToIdealComplement B S hS X I).obj G ⟶
      (restrictToIdealComplement B S hS X I).obj F)
    (hZt : B.Contains (⊤_ Scheme.{u})) (hNo : IsNoetherian B S hS hZt X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1) (k : ℕ)

/-- **The two relocalizations of the chart transport of `θ` along any two morphisms out of a
chart lying over `U = X ∖ V(ℐ)` agree.**

Each component of either relocalization is a component of the chart transport at a slice object
whose source is the source of `Z`, and that source lies over `U` because the chart `A'` it maps
to does — `AlgebraicGeometry.Space.exists_pc_eq_of_over`.  The component determination
`AlgebraicGeometry.Space.chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict` then evaluates both
to the transport of `θ` at that one chart of `U`, with the same identification of it as a
postcomposition, so the two agree.  Nothing about the two morphisms is used. -/
theorem homRestr_chartAlphaSheaf_eq_of_pc_eq
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc A)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc A)) φ =
      chartThetaOver B S hS X I hIc G F θ A)
    {P₀ : SmallEtale B S hS (idealComplement B S hS X I).1} {A' : SmallEtale B S hS X.1}
    (hP₀ : pc B S hS X I P₀ = A') (p q : A' ⟶ A) :
    homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val p
        (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val =
      homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val q
        (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val :=
  Stacks.PresheafOfModules.homRestr_eq_of_forall_app_apply
    (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val p q
    (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val
    fun Z x =>
      let hP := (exists_pc_eq_of_over B S hS X I (Z.unop.hom ≫ eqToHom hP₀.symm)).choose_spec
      let h := fun r : A' ⟶ A =>
        chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict B S hS X I hIc G F θ
          hZt hNo hIq hFq hG A k φ hφ hP (Z.unop.hom ≫ r) x
      (h p).trans (h q).symm

/-- **The two relocalizations of the chart transport of `θ` along the two projections of the
kernel pair `A ⨯ A` agree over the complement of the support of the chartwise sheaf of ideals.**

This is `AlgebraicGeometry.Space.homRestr_chartAlphaSheaf_eq_of_pc_eq` at the chart which that
complement cuts out, which lies over `U = X ∖ V(ℐ)` by
`AlgebraicGeometry.Space.pc_idealComplementChart`, read through the contravariant functoriality
`homRestr_comp` of relocalization.

It is **not** the compatibility condition of
`AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod`, which asks for the agreement over
the whole of `A ⨯ A`: the complement of the support is all of `chartScheme (A ⨯ A)` only when
`ℐ = 𝒪_X`.  Raising the exponent of the ideal is what closes that gap. -/
theorem homRestr_openChartInclusion_homRestr_prod_eq
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc A)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc A)) φ =
      chartThetaOver B S hS X I hIc G F θ A)
    :
    homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val
        (openChartInclusion B S hS X.1 (A ⨯ A)
          ((idealSheafDataOfChart B S hS X I hIc (A ⨯ A)).support.compl :
            (chartScheme (A ⨯ A : SmallEtale B S hS X.1)).Opens))
        (homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val
          (Limits.prod.fst : (A ⨯ A : SmallEtale B S hS X.1) ⟶ A)
          (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val) =
      homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val
        (openChartInclusion B S hS X.1 (A ⨯ A)
          ((idealSheafDataOfChart B S hS X I hIc (A ⨯ A)).support.compl :
            (chartScheme (A ⨯ A : SmallEtale B S hS X.1)).Opens))
        (homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val
          (Limits.prod.snd : (A ⨯ A : SmallEtale B S hS X.1) ⟶ A)
          (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val) :=
  (homRestr_comp (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val
        (openChartInclusion B S hS X.1 (A ⨯ A)
          ((idealSheafDataOfChart B S hS X I hIc (A ⨯ A)).support.compl :
            (chartScheme (A ⨯ A : SmallEtale B S hS X.1)).Opens))
        Limits.prod.fst
        (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val).symm.trans
    ((homRestr_chartAlphaSheaf_eq_of_pc_eq B S hS X I hIc G F θ hZt hNo hIq hFq hG A k φ hφ
          (pc_idealComplementChart B S hS X I hIc (A ⨯ A)
            ((idealSheafDataOfChart B S hS X I hIc (A ⨯ A)).support.compl :
              (chartScheme (A ⨯ A : SmallEtale B S hS X.1)).Opens) le_rfl)
          (openChartInclusion B S hS X.1 (A ⨯ A) _ ≫ Limits.prod.fst)
          (openChartInclusion B S hS X.1 (A ⨯ A) _ ≫ Limits.prod.snd)).trans
      (homRestr_comp (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val
        F.val
        (openChartInclusion B S hS X.1 (A ⨯ A)
          ((idealSheafDataOfChart B S hS X I hIc (A ⨯ A)).support.compl :
            (chartScheme (A ⨯ A : SmallEtale B S hS X.1)).Opens))
        Limits.prod.snd
        (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val))

end ChartAlpha

end AlgebraicGeometry.Space

end
