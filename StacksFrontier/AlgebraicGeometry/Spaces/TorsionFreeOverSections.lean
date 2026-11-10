module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.TorsionFreeStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleTorsionFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupportChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionExact

/-!
# Torsion freeness of a module on an algebraic space, on submodules and from the sections

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and `F`
an `𝒪_X`-module.  Torsion freeness of `F` over `Y` (`AlgebraicGeometry.Space.IsTorsionFreeOver`)
asks that on every commuting square of étale scheme charts `U ⟶ V` of `f`, the stalks of the
restriction `F|_U` have no torsion over the local rings of `V`.

This file proves two facts about that condition, both used in the proof of Stacks 0DM0.

* **It passes to submodules.**  Restriction to an étale scheme chart is left exact, so it carries
  a monomorphism `G ⟶ F` to a monomorphism, and a submodule of a module torsion free over the
  target chart is torsion free over it.
* **Over a valuation ring it can be read on the sections.**  Let `W` be an object of the big fppf
  site with `W ≅ Spec R` for a valuation ring `R`, and let `f : X ⟶ h_W`.  Suppose that for every
  étale scheme chart `V` of `X`, with the induced morphism `β : V ⟶ W`, every nonzero global
  function `t` on `W` acts injectively on the sections of `F` over `V` through its pullback
  `β^*t`.  Then a quasi-coherent `F` is torsion free over `h_W`.  On a square whose target chart
  is `W` itself every regular element of the local ring `𝒪_{W, w}`, a localization of
  `Γ(W, 𝒪_W)`, divides the germ of such a `t`, and the restriction of `F` to the chart has the
  sections of `F` over the Zariski opens of the chart as its sections; this gives torsion
  freeness on those squares.  On an arbitrary square one goes through flatness: by Stacks 0539
  the module is flat over `h_W`, and a flat module is torsion free.

## Main results

* `AlgebraicGeometry.Space.IsTorsionFreeOverOnChartDiagram.of_mono` and
  `AlgebraicGeometry.Space.IsTorsionFreeOver.of_mono`: torsion freeness over the target passes
  to submodules.
* `AlgebraicGeometry.Space.isTorsionFreeOver_restrictToChart_of_injective_smul`: torsion
  freeness of the restriction to a chart over an affine target, from the action of the global
  functions of the target on the sections.
* `AlgebraicGeometry.Space.isTorsionFreeOver_of_injective_smul_of_valuationRing`: over the
  spectrum of a valuation ring, a quasi-coherent module on whose sections the nonzero functions
  of the base act injectively is torsion free over the base.

## References

* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Submodules -/

/-- Restriction of `𝒪_X`-modules to an étale scheme chart carries monomorphisms to
monomorphisms: it is left exact. -/
theorem mono_restrictToChartSchemeFunctor_map {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (U : SmallEtale B S hS X)
    {G F : Modules.{u, u} B S hS X hX} (φ : G ⟶ F) [Mono φ] :
    Mono ((restrictToChartSchemeFunctor.{u, u} B S hS X hX U).map φ) := by
  have := preservesFiniteLimits_restrictToChartSchemeFunctor.{u, u} B S hS X hX U
  infer_instance

/-- **Torsion freeness on one square of charts passes to submodules.** -/
theorem IsTorsionFreeOverOnChartDiagram.of_mono {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {f : X ⟶ Y} {G F : Modules.{u, u} B S hS X hX}
    (φ : G ⟶ F) [Mono φ] {d : ChartDiagram B S hS X Y f}
    (h : IsTorsionFreeOverOnChartDiagram B S hS hX F d) :
    IsTorsionFreeOverOnChartDiagram B S hS hX G d := by
  unfold IsTorsionFreeOverOnChartDiagram at h ⊢
  rw [restrictToChart_eq_restrictToChartScheme B S hS hX G d.U]
  rw [restrictToChart_eq_restrictToChartScheme B S hS hX F d.U] at h
  exact @AlgebraicGeometry.IsTorsionFreeOver.of_mono _ _ _ _ _
    ((restrictToChartSchemeFunctor.{u, u} B S hS X hX d.U).map φ)
    (mono_restrictToChartSchemeFunctor_map hX d.U φ) h

/-- **Torsion freeness over the target passes to submodules.**  If `G ⟶ F` is a monomorphism of
`𝒪_X`-modules and `F` is torsion free over `Y`, so is `G`. -/
theorem IsTorsionFreeOver.of_mono {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {f : X ⟶ Y} {G F : Modules.{u, u} B S hS X hX}
    (φ : G ⟶ F) [Mono φ] (h : IsTorsionFreeOver B S hS hX f F) :
    IsTorsionFreeOver B S hS hX f G :=
  fun d => (h d).of_mono φ

/-- **A subobject of a module torsion free over the target is torsion free over it.** -/
theorem IsTorsionFreeOver.subobject {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {f : X ⟶ Y} {F : Modules.{u, u} B S hS X hX}
    (h : IsTorsionFreeOver B S hS hX f F) (G : Subobject F) :
    IsTorsionFreeOver B S hS hX f (G : Modules.{u, u} B S hS X hX) :=
  h.of_mono G.arrow

/-! ### Torsion freeness read on the sections -/

/-- **Torsion freeness over the target, read on the sections, for schemes.**  This is
`AlgebraicGeometry.isTorsionFreeOverAt_of_forall_dvd_germ` for a morphism of schemes
`g : X ⟶ Y` and an `𝒪_X`-module, with the sections written `Γ(F, O)`. -/
theorem _root_.AlgebraicGeometry.isTorsionFreeOverAt_of_forall_dvd_germ_of_scheme
    {Xs Ys : Scheme.{u}} (g : Xs ⟶ Ys) (F : Xs.Modules) (x : Xs)
    (h : ∀ a : Ys.presheaf.stalk (g x), _root_.IsRegular a →
      ∃ (V : Ys.Opens) (hV : g x ∈ V) (r : Γ(Ys, V)),
        a ∣ Ys.presheaf.germ V (g x) hV r ∧
        ∀ (O : Xs.Opens) (_ : x ∈ O) (hO : O ≤ g ⁻¹ᵁ V),
          Function.Injective fun m : Γ(F, O) => Xs.presheaf.map (homOfLE hO).op (g.app V r) • m) :
    AlgebraicGeometry.IsTorsionFreeOverAt
      (LocallyRingedSpace.forgetToSheafedSpace.map g.toLRSHom) F x :=
  isTorsionFreeOverAt_of_forall_dvd_germ _ F x h

/-- On an open `O` of a scheme `X`, the restriction to `O` of the pullback of a global function
along `g : X ⟶ Y`, read as a global function on the open subscheme `O`, is the pullback along the
composite `O ⟶ X ⟶ Y`. -/
theorem topIso_inv_map_appTop {X Y : Scheme.{u}} (g : X ⟶ Y) (O : X.Opens) (hO : O ≤ g ⁻¹ᵁ ⊤)
    (t : Γ(Y, ⊤)) :
    O.topIso.inv (X.presheaf.map (homOfLE hO).op (g.appTop t)) = O.ι.appTop (g.appTop t) := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
  refine (X.presheaf.map_comp_apply (homOfLE hO).op (eqToHom _).op (g.appTop t)).symm.trans ?_
  exact congrArg (fun φ => X.presheaf.map φ (g.appTop t)) (Subsingleton.elim _ _)

/-- The action of a function `r` on a Zariski open `O` of the scheme of an étale chart `A` on the
sections over `O` of `AlgebraicGeometry.Space.chartRestrictionSheaf` is the action of the
corresponding function on the open subscheme `O` on the sections of the module over the étale
chart that `O` cuts out. -/
theorem chartRestrictionSheaf_smul_up {X : AlgebraicSpaces B S hS}
    (H : Modules.{u, u} B S hS X.1 X.2) (A : SmallEtale B S hS X.1) (O : (chartScheme A).Opens)
    (r : Γ(chartScheme A, O)) (n : H.val.obj (op ((chartOpens B S hS A).obj O))) :
    r • (show Γ(chartRestrictionSheaf B S hS X H A, O) from ULift.up n) =
      (show Γ(chartRestrictionSheaf B S hS X H A, O) from ULift.up
        ((show Γ(chartScheme ((chartOpens B S hS A).obj O), ⊤) from O.topIso.inv r) • n)) := by
  let : Module (Γ(O.toScheme, ⊤) : Type u)
      (H.val.obj (op ((chartOpens B S hS A).obj O)) : Type u) :=
    moduleChartSections B S hS X H ((chartOpens B S hS A).obj O)
  have hr : r = O.topIso.hom (O.topIso.inv r) := (Iso.inv_hom_id_apply O.topIso r).symm
  conv_lhs => rw [hr]
  exact ((chartRestrictionSheafSectionsSemilinear B S hS X H A O).map_smul' _ n).symm

/-- A function on a Zariski open `O` of the scheme of an étale chart `A` acts injectively on the
sections over `O` of `AlgebraicGeometry.Space.chartRestrictionSheaf` as soon as the
corresponding function on the open subscheme `O` acts injectively on the sections of the module
over the étale chart that `O` cuts out. -/
theorem chartRestrictionSheaf_smul_injective {X : AlgebraicSpaces B S hS}
    (H : Modules.{u, u} B S hS X.1 X.2) (A : SmallEtale B S hS X.1) (O : (chartScheme A).Opens)
    (r : Γ(chartScheme A, O))
    (hinj : Function.Injective fun n : H.val.obj (op ((chartOpens B S hS A).obj O)) =>
      (show Γ(chartScheme ((chartOpens B S hS A).obj O), ⊤) from O.topIso.inv r) • n) :
    Function.Injective fun m : Γ(chartRestrictionSheaf B S hS X H A, O) => r • m := by
  rintro ⟨n₁⟩ ⟨n₂⟩ h
  have h4 := (chartRestrictionSheaf_smul_up H A O r n₁).symm.trans
    (h.trans (chartRestrictionSheaf_smul_up H A O r n₂))
  exact congrArg ULift.up (hinj (congrArg ULift.down h4))

/-- **Torsion freeness of the restriction to a chart over an affine target, read on the
sections.**  Let `W` be an object of the big fppf site with affine scheme, `f : X ⟶ h_W` a
morphism from an algebraic space and `H` an `𝒪_X`-module.  Suppose that for every étale scheme
chart `V` of `X`, with the morphism `β : V ⟶ W` induced by `f`, every nonzero global function
`t` on `W` acts injectively on the sections of `H` over `V` through `β^*t`.  Then on every étale
scheme chart `U` of `X`, the restriction `H|_U` is torsion free over `W` through the induced
morphism `α : U ⟶ W`. -/
theorem isTorsionFreeOver_restrictToChart_of_injective_smul {W : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace W) (H : Modules.{u, u} B S hS X.1 X.2)
    (hH : ∀ (V : SmallEtale B S hS X.1) (β : (SmallEtale.toOver B S hS X.1).obj V ⟶ W),
      V.1.hom ≫ f.hom = yoneda.map β → ∀ t : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤),
        t ≠ 0 → Function.Injective fun m : H.val.obj (op V) =>
          (show (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op V) from
            ((BigFppfOver.toScheme B S hS).map β).appTop t) • m)
    (U : SmallEtale B S hS X.1) (α : (SmallEtale.toOver B S hS X.1).obj U ⟶ W)
    (hα : U.1.hom ≫ f.hom = yoneda.map α) :
    AlgebraicGeometry.IsTorsionFreeOver
      (LocallyRingedSpace.forgetToSheafedSpace.map
        ((BigFppfOver.toScheme B S hS).map α).toLRSHom)
      (restrictToChart B S hS X.2 H U) := by
  refine AlgebraicGeometry.IsTorsionFreeOver.of_iso _
    (restrictToChartIsoChartRestrictionSheaf B S hS X H U) (fun u => ?_)
  refine isTorsionFreeOverAt_of_forall_dvd_germ_of_scheme _ _ u (fun a ha => ?_)
  let Ws := (BigFppfOver.toScheme B S hS).obj W
  let α' := (BigFppfOver.toScheme B S hS).map α
  let w : (⊤ : Ws.Opens) := ⟨α' u, trivial⟩
  let := Ws.presheaf.algebra_section_stalk w
  have hloc := (isAffineOpen_top Ws).isLocalization_stalk w
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.mk'_surjective
    ((isAffineOpen_top Ws).primeIdealOf w).asIdeal.primeCompl (show Ws.presheaf.stalk (α' u) from a)
  replace hts : IsLocalization.mk' (Ws.presheaf.stalk (α' u)) t s = a := hts
  have ht : t ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hts
    exact not_isRegular_zero (show _root_.IsRegular (0 : Ws.presheaf.stalk (α' u)) from hts ▸ ha)
  refine ⟨⊤, trivial, t, ⟨algebraMap Γ(Ws, ⊤) (Ws.presheaf.stalk (α' u)) (s : Γ(Ws, ⊤)), ?_⟩, ?_⟩
  · change Ws.presheaf.germ ⊤ (α' u) trivial t = _
    rw [← hts]
    exact (IsLocalization.mk'_spec (Ws.presheaf.stalk (α' u)) t s).symm
  · intro O huO hO
    let β : (SmallEtale.toOver B S hS X.1).obj ((chartOpens B S hS U).obj O) ⟶ W :=
      chartOpenOverι B S hS U O ≫ α
    have hβ : ((chartOpens B S hS U).obj O).1.hom ≫ f.hom = yoneda.map β := by
      change (yoneda.map (chartOpenOverι B S hS U O) ≫ U.obj.hom) ≫ f.hom = _
      rw [Category.assoc, hα]
      exact (yoneda.map_comp _ _).symm
    have e2 : ((BigFppfOver.toScheme B S hS).map β).appTop t =
        O.ι.appTop (α'.appTop t) := by
      simp only [β]
      rfl
    let r : Γ(chartScheme U, O) := (chartScheme U).presheaf.map
      (homOfLE (show O ≤ α' ⁻¹ᵁ ⊤ from hO)).op (α'.appTop t)
    have e4 : (show Γ(chartScheme ((chartOpens B S hS U).obj O), ⊤) from O.topIso.inv r) =
        ((BigFppfOver.toScheme B S hS).map β).appTop t :=
      (topIso_inv_map_appTop α' O _ t).trans e2.symm
    have hinj' : Function.Injective fun n : H.val.obj (op ((chartOpens B S hS U).obj O)) =>
        (show Γ(chartScheme ((chartOpens B S hS U).obj O), ⊤) from O.topIso.inv r) • n := by
      rw [e4]
      exact hH _ β hβ t ht
    exact chartRestrictionSheaf_smul_injective H U O _ hinj'

/-- **Over a valuation ring, torsion freeness is read on the sections.**  Let `R` be a valuation
ring, `W` an object of the big fppf site whose scheme is `Spec R`, `f : X ⟶ h_W` a morphism from
an algebraic space and `H` a quasi-coherent `𝒪_X`-module.  Suppose that for every étale scheme
chart `V` of `X`, with the morphism `β : V ⟶ W` induced by `f`, every nonzero global function
`t` on `W` acts injectively on the sections of `H` over `V` through `β^*t`.  Then `H` is torsion
free over `h_W`, on every commuting square of étale scheme charts.

On the squares whose target chart is `W` this is
`AlgebraicGeometry.Space.isTorsionFreeOver_restrictToChart_of_injective_smul`; it gives
flatness over `h_W` by Stacks 0539, and a flat module is torsion free on every square. -/
theorem isTorsionFreeOver_of_injective_smul_of_valuationRing {R : Type u} [CommRing R]
    [IsDomain R] [ValuationRing R] {W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ Spec (CommRingCat.of R))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace W) (H : Modules.{u, u} B S hS X.1 X.2)
    (hqc : H.IsQuasicoherentOnSite)
    (hH : ∀ (V : SmallEtale B S hS X.1) (β : (SmallEtale.toOver B S hS X.1).obj V ⟶ W),
      V.1.hom ≫ f.hom = yoneda.map β → ∀ t : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤),
        t ≠ 0 → Function.Injective fun m : H.val.obj (op V) =>
          (show (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op V) from
            ((BigFppfOver.toScheme B S hS).map β).appTop t) • m) :
    IsTorsionFreeOver B S hS X.2 f.hom H := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := IsAffine.of_isIso e.hom
  exact IsFlatOver.isTorsionFreeOver
    (isFlatOver_of_isTorsionFreeOver_restrictToChart_of_valuationRing e f H hqc
      (fun U α hα => isTorsionFreeOver_restrictToChart_of_injective_smul f H hH U α hα))

end AlgebraicGeometry.Space

end
