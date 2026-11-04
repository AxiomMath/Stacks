module

public import StacksFrontier.AlgebraicGeometry.DenseDenominators.FromMorphism
public import StacksFrontier.AlgebraicGeometry.Limits.ResidueFieldSpreading
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsShortExactSchemeSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparisonMapSpaceChain

/-!
# The naturality square of Stacks 04CS on sections: the joins and the spaces side

Pieces of the sections identity which closes the naturality square of Stacks 04CS for the mate
comparison of Stacks 03LC (1)
(`AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_square_of_postcomp`).  Every
crossing between the Zariski spelling and the space-site spelling of a group of sections is made
in a lemma whose module is a *variable*: at a concrete module such a crossing costs more than a
declaration's heartbeat budget, while on a variable it is free.  Equalities between sections in
different spellings are joined with `subst` or through `HEq`, never with `Eq.trans`, whose middle
argument re-checks the shared type at the concrete module.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u


namespace AlgebraicGeometry

/-- **Pulling back a function along two morphisms into an open and its preimage.**  If
`g : T ⟶ O` and `h : T ⟶ f⁻¹O` agree after the inclusion of `O` and after the inclusion of
`f⁻¹O` followed by `f`, then pulling back along `g` the function on `O` that `a ∈ Γ(Y, O)` is,
and pulling back along `h` the function `f♯ a` on `f⁻¹O`, give the same global function on `T`. -/
theorem Scheme.Opens.Γ_map_topIso_inv_of_comp {X Y T : Scheme.{u}} (f : X ⟶ Y) (O : Y.Opens)
    (g : T ⟶ O.toScheme) (h : T ⟶ (f ⁻¹ᵁ O).toScheme)
    (w : g ≫ O.ι = h ≫ (f ⁻¹ᵁ O).ι ≫ f) (a : Γ(Y, O)) :
    (Scheme.Γ.map g.op).hom (O.topIso.inv a) =
      (Scheme.Γ.map h.op).hom ((f ⁻¹ᵁ O).topIso.inv (f.app O a)) := by
  have key : ∀ {Y' : Scheme.{u}} {Ω : Y'.Opens} (π : T ⟶ Ω.toScheme) (b : Γ(Y', Ω)),
      ((π ≫ Ω.ι).appLE Ω ⊤ (by simp)).hom b = (Scheme.Γ.map π.op).hom (Ω.topIso.inv b) :=
    fun π b => by
    rw [Stacks.DenseDenominators.appLE_eq_topIso_inv_appTop]
    rfl
  have l₃ := congrArg (·.hom a)
    (Scheme.Hom.comp_appLE (h ≫ (f ⁻¹ᵁ O).ι) f O ⊤ (by simp))
  have l₄ := congrArg (fun m : Γ(Y, O) ⟶ Γ(T, ⊤) => m.hom a)
    (Scheme.Hom.appLE_eq_of_eq (w.trans (Category.assoc _ _ _).symm) (by simp) (by simp))
  simp only [CommRingCat.comp_apply] at l₃
  exact (key g a).symm.trans (l₄.trans (l₃.trans (key h _)))

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


/-- **A morphism followed by an induced one, on a section**, through `HEq`: if `c` carries `w` to
a section `r` of the reference module `M` over `A`, and `t` is restriction along an arrow
`A' ⟶ A`, then `c ≫ t` carries `w` to the restriction of `r`. -/
theorem heq_comp_app_of_induced {X : Scheme.{u}} {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R}
    {N₁ N₂ N₃ : X.Modules} {c : N₁ ⟶ N₂} {t : N₂ ⟶ N₃} {O : X.Opens} {A A' : C}
    (ht : Stacks.SectionsComponents.Induced M t (op O) A A') {w : Γ(N₁, O)}
    {r : M.val.obj (op A)} (hc : HEq (c.app O w) r) :
    ∃ u : A' ⟶ A, HEq ((c ≫ t).app O w) (M.val.map u.op r) := by
  obtain ⟨u, e₁, e₂, hu⟩ := ht
  refine ⟨u, ?_⟩
  have h3 := (cast_heq e₁ (c.app O w)).trans hc
  have h4 := congrArg (M.val.map u.op) (eq_of_heq h3)
  exact (cast_heq e₂ _).symm.trans (heq_of_eq ((hu (c.app O w)).trans h4))

section ChartStructureSharp

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03G8 (2) on sections, read through the chart projection.**  For a representable
morphism `f : X ⟶ Y` and an étale chart `V` of `Y`, the chart projection of the structure map
`f♯` applied to a regular function `x` on `V` is the pullback of `x` along the cartesian
projection `X ×_Y V ⟶ V`. -/
theorem chartSetProj_structureSharpSet (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (V : SmallEtale B S hS Y.1) (x : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    chartSetProj B S hS f hf (structureSetSheaf B S hS X) V
        ((structureSharpSet B S hS f).hom.app (op V) x) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op).hom x := by
  have h1 : (structureSharpSet B S hS f).hom.app (op V) x =
      ((smallEtaleDirectImageRanIso B S hS f).inv.app (structureSetSheaf B S hS X)).hom.app
        (op V) (structureMapApp B S hS f V x) := by
    rw [structureSharpSet_eq]
    rfl
  rw [h1]
  have h2 : ((smallEtaleComparisonRanIso B S hS X).hom.app (structureSetSheaf B S hS X)).hom.app
      (op (chartBaseChange B S hS f V))
        (((smallEtaleDirectImageRanIso B S hS f).inv.app (structureSetSheaf B S hS X)).hom.app
          (op V) (structureMapApp B S hS f V x)) = structureMapApp B S hS f V x :=
    congrArg (fun t => t.hom.app (op (chartBaseChange B S hS f V)) (structureMapApp B S hS f V x))
      ((smallEtaleComparisonRanIso B S hS X).inv_hom_id_app (structureSetSheaf B S hS X))
  refine (congrArg (chartRanApp B S hS f hf (structureSetSheaf B S hS X).obj V) h2).trans ?_
  refine Eq.trans ?_ (chartProjection_structureMapApp_chartBaseChangeArrow B S hS f hf V x)
  exact (chartProjection_app_apply B S hS f V (chartBaseChangeArrow B S hS f hf V) _).symm

end ChartStructureSharp

section Square

variable {U V W : BigFppfOver B S hS}

/-- Sections of the direct image along `ψ` of the Zariski restriction of `M`, over `O`, are
sections of the Zariski restriction over `ψ^{-1}O`. -/
theorem eq_of_eq_preimage (ψ : U ⟶ V)
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (x y : Γ(((((representedModuleSiteEquivalence B S hS U).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
          Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).obj M), O))
    (h : (x : Γ((((representedModuleSiteEquivalence B S hS U).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M),
                ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))) = y) : x = y := h

/-- Sections of the Zariski restriction of `M` over `P` are sections of `M` over the chart `P`
cuts out. -/
theorem eq_of_eq_representedOpensObj_preimage (ψ : U ⟶ V)
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (x y : Γ((((representedModuleSiteEquivalence B S hS U).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M),
                ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)))
    (h : (x : (M.val.obj (op (representedOpensObj B S hS U
        ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))))) = y) : x = y := h

/-- Sections of the direct image along `ψ` of the Zariski restriction of `M` over `O` agree as soon
as they agree read over the chart `ψ^{-1}O` cuts out. -/
theorem eq_of_eq_representedOpensObj_pushforward (ψ : U ⟶ V)
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (x y : Γ(((((representedModuleSiteEquivalence B S hS U).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
          Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).obj M), O))
    (h : (x : (M.val.obj (op (representedOpensObj B S hS U
        ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))))) = y) : x = y :=
  eq_of_eq_preimage B S hS ψ M O x y (eq_of_eq_representedOpensObj_preimage B S hS ψ M O x y h)

/-- **The join of the Zariski chain and the spaces chain of the sections identity of Stacks 04CS**,
on variables: both sides read over the chart the preimage open cuts out, the spaces side reached
through an equation in the spelling of the factors of `γ⁻¹`. -/
theorem eq_of_representedOpensObj_preimage_join (ψ : U ⟶ V)
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (x y : Γ(((((representedModuleSiteEquivalence B S hS U).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
          Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).obj M), O))
    (y'' : Γ(((((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
          Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).obj M), O))
    (z : (M.val.obj (op (representedOpensObj B S hS U
        ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)))))
    (hx : (x : (M.val.obj (op (representedOpensObj B S hS U
        ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))))) = z) (h3 : y = y'')
    (h4 : (y'' : (M.val.obj (op (representedOpensObj B S hS U
        ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))))) = z) : x = y := by
  subst h4
  subst h3
  exact eq_of_eq_representedOpensObj_pushforward B S hS ψ M O x y hx

/-- `AlgebraicGeometry.Space.eq_of_representedOpensObj_preimage_join` with the spaces chain given
as an `HEq`. -/
theorem eq_of_representedOpensObj_preimage_join_heq (ψ : U ⟶ V)
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (x y : Γ(((((representedModuleSiteEquivalence B S hS U).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
          Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).obj M), O))
    (y'' : Γ(((((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
          Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).obj M), O))
    (z : (M.val.obj (op (representedOpensObj B S hS U
        ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)))))
    (hx : (x : (M.val.obj (op (representedOpensObj B S hS U
        ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))))) = z) (h3 : y = y'')
    (h4 : HEq y'' z) : x = y :=
  eq_of_representedOpensObj_preimage_join B S hS ψ M O x y y'' z hx h3 (eq_of_heq h4)

/-- The chart factor of `γ⁻¹` over an open is the morphism itself over the chart the open cuts
out, on variables. -/
theorem restrictModule_inverse_map_app_eq (C : BigFppfOver B S hS)
    {N₁ N₂ : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2} (h : N₁ ⟶ N₂)
    (O : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (v : N₁.val.obj (op (representedOpensObj B S hS C O))) :
    (((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS C).inverse.map h)).app O v :
        N₂.val.obj (op (representedOpensObj B S hS C O))) =
      h.val.app (op (representedOpensObj B S hS C O)) v :=
  rfl

/-- The chart factor of `γ⁻¹` over an open, transported along an `HEq` of its value, on
variables: the one crossing between the Zariski and the space-side spelling is paid here, where
the target module is a variable. -/
theorem heq_restrictModule_inverse_map_app (C : BigFppfOver B S hS)
    {N₁ N₂ : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2} (h : N₁ ⟶ N₂)
    (O : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (v : N₁.val.obj (op (representedOpensObj B S hS C O))) {T : Type u} {r : T}
    (hr : HEq (h.val.app (op (representedOpensObj B S hS C O)) v) r) :
    HEq (((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS C).inverse.map h)).app O v) r :=
  (heq_of_eq (restrictModule_inverse_map_app_eq B S hS C h O v)).trans hr

/-- **The chart factor of `γ⁻¹` over an open is the chart projection of Stacks 03LU**, as an `HEq`
of sections in the two spellings. -/
theorem heq_chart_app (ψ : U ⟶ V)
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (w : ((smallEtaleDirectImage B S hS (representedSpaceMap B S hS ψ)).obj
      (moduleSetSheaf B S hS _ M)).obj.obj (op (representedOpensObj B S hS V O))) : HEq
          (Scheme.Modules.Hom.app ((_root_.AlgebraicGeometry.SmallEtale.restrictModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
          ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS ψ)
            (relativelyRepresentable_yoneda_map B S hS ψ)).hom.app M))) O w)
                (chartSetProj B S hS (representedSpaceMap B S hS ψ)
          (relativelyRepresentable_yoneda_map B S hS ψ) (moduleSetSheaf B S hS _ M)
          (representedOpensObj B S hS V O) w) :=
  heq_restrictModule_inverse_map_app B S hS V ((modulePushforwardChartIso B S hS
    (representedSpaceMap B S hS ψ) (relativelyRepresentable_yoneda_map B S hS ψ)).hom.app M) O w
        (heq_of_eq (modulePushforwardChartIso_hom_app_chartSetProj B S hS
        (representedSpaceMap B S hS ψ)
    (relativelyRepresentable_yoneda_map B S hS ψ) M (representedOpensObj B S hS V O) w))

/-- **The spaces side of the sections identity of Stacks 04CS, past the comparison `γ⁻¹`**, on a
variable module: the chart factor followed by the tail is the chart projection followed by
restriction along an arrow of the small étale site of `yoneda.obj U`. -/
theorem tail_chart_app (ψ : U ⟶ V)
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (w : ((smallEtaleDirectImage B S hS (representedSpaceMap B S hS ψ)).obj
      (moduleSetSheaf B S hS _ M)).obj.obj (op (representedOpensObj B S hS V O))) :
    ∃ u : representedOpensObj B S hS U ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O) ⟶
        (smallBaseChange B S hS
          (representedSpaceMap B S hS ψ) (relativelyRepresentable_yoneda_map B S hS ψ)).obj
            (representedOpensObj B S hS V O),
      HEq ((((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
            ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
              ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS ψ)
                (relativelyRepresentable_yoneda_map B S hS ψ)).hom.app M))) ≫
                    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
                ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
                    ((smallBaseChangeModulePushforward.{u, u} B S hS
                            (representedSpaceMap B S hS ψ)
                            (relativelyRepresentable_yoneda_map B S hS ψ)).map
                          ((representedSmallEtaleModuleEquivalence B S hS U).counitInv.app M) ≫
                      (representedModulePushforwardSquareRestrictIso B S hS ψ
                            (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
                          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M)) ≫
                  (representedModulePushforwardSquareInverseIsoUnit B S hS ψ).inv.app M) ≫
            (representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).inv.app M)).app O w)
        (M.val.map u.op (chartSetProj B S hS (representedSpaceMap B S hS ψ)
          (relativelyRepresentable_yoneda_map B S hS ψ) (moduleSetSheaf B S hS _ M)
          (representedOpensObj B S hS V O) w)) :=
  heq_comp_app_of_induced
    (induced_representedRestrictModuleBaseChangeIso_inv_tail B S hS ψ M O)
    (heq_chart_app B S hS ψ M O w)

/-- **The canonical derivation `d^a`, pushed forward along `ψ̃`, read through the chart projection
and restricted along an arrow into the base-changed chart**: it is `d^a` of the pullback of the
function along the cartesian projection, restricted along that arrow.  Stacks 03G8 (2) and the
naturality of the chart projection. -/
theorem map_chartSetProj_directImage_representedUniversalDerivation {D : BigFppfOver B S hS}
    (α : U ⟶ D) (ψ : U ⟶ V) (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    {A' : SmallEtale B S hS (schemeSpace U).1}
    (u : A' ⟶ (smallBaseChange B S hS (representedSpaceMap B S hS ψ)
      (relativelyRepresentable_yoneda_map B S hS ψ)).obj (representedOpensObj B S hS V O))
    (x : (structureSetSheaf B S hS (schemeSpace V)).obj.obj (op (representedOpensObj B S hS V O))) :
    (representedRelativeDifferentials B S hS α).val.map u.op
        (chartSetProj B S hS (representedSpaceMap B S hS ψ)
          (relativelyRepresentable_yoneda_map B S hS ψ)
          (moduleSetSheaf B S hS _ (representedRelativeDifferentials B S hS α))
          (representedOpensObj B S hS V O)
          (((smallEtaleDirectImage B S hS (schemeSpaceMap ψ)).map
              (representedUniversalDerivationHom B S hS α)).hom.app
            (op (representedOpensObj B S hS V O))
            ((structureSharpSet B S hS (schemeSpaceMap ψ)).hom.app
              (op (representedOpensObj B S hS V O)) x))) =
      (representedUniversalDerivation B S hS α).d (X := op A')
        ((structureSetSheaf B S hS (schemeSpace U)).obj.map u.op
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            ((relativelyRepresentable_yoneda_map B S hS ψ).snd
              (representedOpensObj B S hS V O).1.hom)).op).hom x)) := by
  have h1 := chartSetProj_naturality B S hS (representedSpaceMap B S hS ψ)
    (relativelyRepresentable_yoneda_map B S hS ψ) (representedUniversalDerivationHom B S hS α)
    (representedOpensObj B S hS V O)
    ((structureSharpSet B S hS (schemeSpaceMap ψ)).hom.app
      (op (representedOpensObj B S hS V O)) x)
  have h2 := chartSetProj_structureSharpSet B S hS (representedSpaceMap B S hS ψ)
    (relativelyRepresentable_yoneda_map B S hS ψ) (representedOpensObj B S hS V O) x
  have h3 := (representedUniversalDerivation B S hS α).d_map u.op
    ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_yoneda_map B S hS ψ).snd
        (representedOpensObj B S hS V O).1.hom)).op).hom x)
  exact (congrArg ((representedRelativeDifferentials B S hS α).val.map u.op) (h1.trans
    (congrArg ((representedUniversalDerivationHom B S hS α).hom.app
      (op ((smallBaseChange B S hS (representedSpaceMap B S hS ψ)
        (relativelyRepresentable_yoneda_map B S hS ψ)).obj (representedOpensObj B S hS V O))))
      h2))).trans h3.symm

/-- The structure morphism, in the big fppf category, of the chart an open cuts out. -/
abbrev representedOpensObjHom (C : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj C).Opens) :
    (representedOpensObj B S hS C O).1.left ⟶ C :=
  ((Over.iteratedSliceEquiv C).inverse.obj
      ((BigEtaleOver.IsEtaleOver (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj C) C.left.property).ι.obj
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property O))).hom

/-- **The square of a Zariski open, its preimage and the base-changed chart commutes in the big
fppf category**: an arrow `u` of the small étale site of `yoneda.obj U` from the chart `ψ^{-1}O`
cuts out into the base change along `ψ̃` of the chart `O` cuts out, followed by the cartesian
projection and the inclusion of `O`, is the inclusion of `ψ^{-1}O` followed by `ψ`. -/
theorem representedOpensObjHom_comp_of_smallBaseChange (ψ : U ⟶ V)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (u : representedOpensObj B S hS U ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O) ⟶
        (smallBaseChange B S hS
          (representedSpaceMap B S hS ψ) (relativelyRepresentable_yoneda_map B S hS ψ)).obj
            (representedOpensObj B S hS V O)) :
    u.hom.left ≫ (relativelyRepresentable_yoneda_map B S hS ψ).snd
        (representedOpensObj B S hS V O).1.hom ≫ representedOpensObjHom B S hS V O =
      representedOpensObjHom B S hS U ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O) ≫ ψ := by
  apply yoneda.map_injective
  have hw := (relativelyRepresentable_yoneda_map B S hS ψ).w (representedOpensObj B S hS V O).1.hom
  have hu := CostructuredArrow.w u.hom
  simp only [Functor.map_comp]
  change yoneda.map u.hom.left ≫ yoneda.map ((relativelyRepresentable_yoneda_map B S hS ψ).snd
      (representedOpensObj B S hS V O).1.hom) ≫ (representedOpensObj B S hS V O).1.hom =
    (representedOpensObj B S hS U ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)).1.hom ≫ yoneda.map ψ
  exact (congrArg (yoneda.map u.hom.left ≫ ·) hw.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ yoneda.map ψ) hu))

/-- A presheaf of rings does nothing along a morphism which is the identity up to `HEq`. -/
theorem heq_map_op_apply_of_heq_id {C : Type*} [Category C] (F : Cᵒᵖ ⥤ CommRingCat.{u})
    {X Y : C} (e : X = Y) (k : X ⟶ Y) (hk : HEq k (𝟙 Y)) (z : F.obj (op Y)) :
    HEq (F.map k.op z) z := by
  subst e
  rw [eq_of_heq hk]
  simp

/-- The structure sheaf of the small étale site of a scheme does nothing along the counit of the
comparison of sites at the chart an open cuts out: that counit is the identity. -/
theorem commRingStructureSheaf_map_counit_opensObj (C : BigFppfOver B S hS)
    (Q : ((BigFppfOver.toScheme B S hS).obj C).Opens) (z : Γ(Q.toScheme, ⊤)) :
    HEq ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj.map
        ((representedSmallEtaleEquivalence B S hS C).counit.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property Q)).op z) z :=
  heq_map_op_apply_of_heq_id (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
      (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj rfl
    ((representedSmallEtaleEquivalence B S hS C).counit.app
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property Q))
    (heq_of_eq (representedSmallEtaleEquivalence_counit_app B S hS C
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property Q))) z

/-- **The two regular functions the two sides of the sections identity of Stacks 04CS evaluate
`d^a` on agree**: the pullback of `a` along the cartesian projection, restricted along `u`, is the
Zariski pullback `ψ♯ a` on `ψ^{-1}O`. -/
theorem structureSetSheaf_map_cartesianProjection_eq (ψ : U ⟶ V)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (u : representedOpensObj B S hS U ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O) ⟶
        (smallBaseChange B S hS
          (representedSpaceMap B S hS ψ) (relativelyRepresentable_yoneda_map B S hS ψ)).obj
            (representedOpensObj B S hS V O))
    (a : Γ(((BigFppfOver.toScheme B S hS).obj V), O)) :
    (structureSetSheaf B S hS (schemeSpace U)).obj.map u.op
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_yoneda_map B S hS ψ).snd
            (representedOpensObj B S hS V O).1.hom)).op).hom
          ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj.map
            ((representedSmallEtaleEquivalence B S hS V).counit.app
                (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property O)).op
            (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).hom.app (op O)).hom a))) =
      ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map
          ((representedSmallEtaleEquivalence B S hS U).counit.app
              (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property
              ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))).op
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app
              (op ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))).hom
            ((((BigFppfOver.toScheme B S hS).map ψ).app O).hom a)) :
        (structureSetSheaf B S hS (schemeSpace U)).obj.obj
          (op (representedOpensObj B S hS U ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)))) := by
  have c1 := eq_of_heq (commRingStructureSheaf_map_counit_opensObj B S hS V O (O.topIso.inv a))
  have c2 := eq_of_heq (commRingStructureSheaf_map_counit_opensObj B S hS U
      ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)
    (((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O).topIso.inv
        ((((BigFppfOver.toScheme B S hS).map ψ).app O).hom a)))
  have hsq := congrArg (BigFppfOver.toScheme B S hS).map
    (representedOpensObjHom_comp_of_smallBaseChange B S hS ψ O u)
  simp only [Functor.map_comp] at hsq
  have key := Scheme.Opens.Γ_map_topIso_inv_of_comp ((BigFppfOver.toScheme B S hS).map ψ) O
    ((BigFppfOver.toScheme B S hS).map u.hom.left ≫ (BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_yoneda_map B S hS ψ).snd (representedOpensObj B S hS V O).1.hom))
    (𝟙 _) ((Category.assoc _ _ _).trans (hsq.trans (Category.id_comp _).symm)) a
  exact (congrArg (fun z => (structureSetSheaf B S hS (schemeSpace U)).obj.map u.op
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_yoneda_map B S hS ψ).snd
          (representedOpensObj B S hS V O).1.hom)).op).hom z)) c1).trans (key.trans c2.symm)

/-- **The spaces side of the sections identity of Stacks 04CS past `γ⁻¹`, evaluated**: on the
direct image of `d^a` of `α` applied to `ψ̃♯ x`, the chart factor and the tail give `d^a` of `α` on
any function which every restriction of the cartesian pullback of `x` equals. -/
theorem heq_tail_chart_representedUniversalDerivation {D : BigFppfOver B S hS} (α : U ⟶ D)
    (ψ : U ⟶ V) (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (x : (structureSetSheaf B S hS (schemeSpace V)).obj.obj (op (representedOpensObj B S hS V O)))
    (z₀ : (structureSetSheaf B S hS (schemeSpace U)).obj.obj
      (op (representedOpensObj B S hS U ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))))
    (hz : ∀ u : representedOpensObj B S hS U ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O) ⟶
        (smallBaseChange B S hS
          (representedSpaceMap B S hS ψ) (relativelyRepresentable_yoneda_map B S hS ψ)).obj
            (representedOpensObj B S hS V O),
      (structureSetSheaf B S hS (schemeSpace U)).obj.map u.op
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_yoneda_map B S hS ψ).snd
            (representedOpensObj B S hS V O).1.hom)).op).hom x) = z₀) :
    HEq ((((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
            ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
              ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS ψ)
                (relativelyRepresentable_yoneda_map B S hS ψ)).hom.app
                    (representedRelativeDifferentials B S hS α)))) ≫
                    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
                ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
                    ((smallBaseChangeModulePushforward.{u, u} B S hS
                            (representedSpaceMap B S hS ψ)
                            (relativelyRepresentable_yoneda_map B S hS ψ)).map
                          ((representedSmallEtaleModuleEquivalence B S hS U).counitInv.app
                              (representedRelativeDifferentials B S hS α)) ≫
                      (representedModulePushforwardSquareRestrictIso B S hS ψ
                            (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
                          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj
                              (representedRelativeDifferentials B S hS α))) ≫
                  (representedModulePushforwardSquareInverseIsoUnit B S hS ψ).inv.app
                      (representedRelativeDifferentials B S hS α)) ≫
            (representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).inv.app
                (representedRelativeDifferentials B S hS α))).app O
                (((smallEtaleDirectImage B S hS (schemeSpaceMap ψ)).map
              (representedUniversalDerivationHom B S hS α)).hom.app
            (op (representedOpensObj B S hS V O))
            ((structureSharpSet B S hS (schemeSpaceMap ψ)).hom.app
              (op (representedOpensObj B S hS V O)) x)))
      ((representedUniversalDerivation B S hS α).d
        (X := op (representedOpensObj B S hS U
          ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))) z₀) := by
  obtain ⟨u, h⟩ := tail_chart_app B S hS ψ (representedRelativeDifferentials B S hS α) O
      (((smallEtaleDirectImage B S hS (schemeSpaceMap ψ)).map
              (representedUniversalDerivationHom B S hS α)).hom.app
            (op (representedOpensObj B S hS V O))
            ((structureSharpSet B S hS (schemeSpaceMap ψ)).hom.app
              (op (representedOpensObj B S hS V O)) x))
  exact h.trans (heq_of_eq ((map_chartSetProj_directImage_representedUniversalDerivation B S hS
    α ψ O u x).trans (congrArg (representedUniversalDerivation B S hS α).d (hz u))))

/-- **The naturality square of Stacks 04CS for the mate comparison of Stacks 03LC (1)**, for every
composable pair `ψ : U ⟶ V`, `χ : V ⟶ W` of morphisms of schemes of the site.  Its one input,
the identity of Zariski derivations of
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_square_of_postcomp`, is checked on
the universal differential `d_{V/W}(a)` over every open `O`: the Zariski chain and the spaces
chain both end at the canonical derivation `d^a` of `ψ ≫ χ` over the chart `ψ^{-1}O` cuts out,
on the Zariski pullback `ψ♯ a`. -/
theorem representedAssociatedModulePullbackMate_square (ψ : U ⟶ V) (χ : V ⟶ W) :
    (representedAssociatedModulePullbackMateIso B S hS ψ).hom.app
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ)) ≫
        (representedAssociatedModule B S hS U (schemeSpace U).property).map
          (schemeChartDifferentialsMap B S hS ψ χ) =
      (modulePullback B S hS (schemeSpaceMap ψ)).map
          (representedDifferentialsComparison B S hS χ) ≫
        pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
          (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom :=
  representedAssociatedModulePullbackMate_square_of_postcomp B S hS ψ χ
    (Scheme.Hom.postcomp_universalRelativeDerivation_eq_of_app_d _ _ _ fun O a => by
      have z1 := zariskiChain_homEquiv_schemeChartDifferentialsMap B S hS ψ χ O a
      have z2 := zariskiChain_representedAssociatedModuleAdjunction_unit B S hS (ψ ≫ χ)
          ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)
        ((((BigFppfOver.toScheme B S hS).map ψ).app O).hom a)
      have z3 := zariskiChain_associatedModuleAdjunction_unit_d B S hS (ψ ≫ χ)
          ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)
        ((((BigFppfOver.toScheme B S hS).map ψ).app O).hom a)
      have z45 := spaceChain_unit_representedUniversalDerivation B S hS (ψ ≫ χ)
          ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)
        ((((BigFppfOver.toScheme B S hS).map ψ).app O).hom a)
      have hx := eq_representedOpensObj_trans B S hS
        (representedRelativeDifferentials B S hS (ψ ≫ χ))
            ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O) _ _ _ (z1.trans (z2.trans z3)) z45
      have h3 := spaceChain_chartFirst B S hS ψ χ O a
      have h4 := heq_tail_chart_representedUniversalDerivation B S hS (ψ ≫ χ) ψ O
          ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj.map
            ((representedSmallEtaleEquivalence B S hS V).counit.app
                (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property O)).op
            (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).hom.app (op O)).hom a))
              ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
              (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map
          ((representedSmallEtaleEquivalence B S hS U).counit.app
              (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property
              ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))).op
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app
              (op ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O))).hom
            ((((BigFppfOver.toScheme B S hS).map ψ).app O).hom a)))
        (fun u => structureSetSheaf_map_cartesianProjection_eq B S hS ψ O u a)
      exact eq_of_representedOpensObj_preimage_join_heq B S hS ψ
        (representedRelativeDifferentials B S hS (ψ ≫ χ)) O _ _ _ _ hx h3 h4)

end Square

/-- **The scheme-to-space step of Stacks 04CS for the comparison map of Stacks 04CX.**  For every
composable pair `ψ : U ⟶ V`, `χ : V ⟶ W` of morphisms of schemes of the site, a monomorphic
Zariski comparison map `ψ^*Ω_{V/W} ⟶ Ω_{U/W}` of Stacks 01UV gives a monomorphic comparison map
of `ψ` read between represented algebraic spaces: the naturality square
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_square` and
`AlgebraicGeometry.Space.mono_pullbackDifferentialsMap_of_mate_square`. -/
theorem pullbackDifferentialsMapSchemeSpaceComparison :
    PullbackDifferentialsMapSchemeSpaceComparison B S hS :=
  fun _ _ _ ψ χ hm => mono_pullbackDifferentialsMap_of_mate_square B S hS ψ χ
    (representedAssociatedModulePullbackMate_square B S hS ψ χ) hm

section ShortExact

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **Stacks 06BI.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over `S`
with `f` formally smooth.  Then the sequence `0 ⟶ f^*Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0` of
Stacks 05Z8 is short exact.

The first map is a monomorphism étale locally: on compatible étale charts `U ⟶ V ⟶ W` with
`U ⟶ V` formally smooth (Stacks 061K) it is the scheme statement (Stacks 02HP), carried to the
spaces by Stacks 04CU and 04CS
(`AlgebraicGeometry.Space.pullbackDifferentialsMapSchemeSpaceComparison`); exactness at the other
two terms is Stacks 05Z8. -/
@[stacks 06BI]
theorem triangleDifferentials_shortExact_of_formallySmooth (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : FormallySmooth f.hom) :
    ∃ h : pullbackDifferentialsMap B S hS f g ≫ toRelativeDifferentials B S hS f g = 0,
      (ShortComplex.mk _ _ h).ShortExact :=
  triangleDifferentials_shortExact_of_schemeSpaceComparison B S hS f g hf
    (pullbackDifferentialsMapSchemeSpaceComparison B S hS)

end ShortExact


end AlgebraicGeometry.Space

end
