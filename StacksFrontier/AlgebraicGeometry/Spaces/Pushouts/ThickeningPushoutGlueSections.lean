module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutSpaceModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSections
public import StacksFrontier.RingTheory.MilnorPatching.BaseChangeGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceQuotientQuasicoherent

/-!
# Sections of the glued module over the charts of a pushout along a thickening

The sections of the glued module `G = a_*A ×_{(c ≫ a)_*c^*A} b_*B'` over a chart `W` of `P`
lying over a chart `T` of `Y'`: they are the fibre product of the sections of `A` over `W_Y` and of
`B'` over `W_{Z'}` over the sections of `c^*A` over `W_Z` (`isGlued`).  When `W` and `T` are
affine and the pieces are quasi-coherent, the relative Milnor square of the charts turns this into
the two base-change identities of Stacks 08KM (`isBaseChangeAlong_glueFst_glueSnd`) and, for
pieces flat over `Y` and `Z'`, into flatness of `G(W)` over `Γ(T)` (Stacks 07RW,
`flat_glue_sections`).

## References

* [Stacks Project, Tag 08KM](https://stacks.math.columbia.edu/tag/08KM)
* [Stacks Project, Tag 07RW](https://stacks.math.columbia.edu/tag/07RW)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- The ambient-universe abelian structure on sheaves of modules would be selected ahead of
-- `SheafOfModules.instAbelian` for the `𝒪`-modules here, whose sections live in the universe of
-- the schemes.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ThickeningPushoutSpaces

variable {Z Z' Y Y' : BigFppfOver B S hS} {i : Z ⟶ Z'} {f : Z ⟶ Y} {g : Z' ⟶ Y'} {h : Y ⟶ Y'}
  {P V U' U : AlgebraicSpaces B S hS} {p : P ⟶ (schemeSpaceFunctor B S hS).obj Y'}
  {pV : V ⟶ (schemeSpaceFunctor B S hS).obj Y} {pU' : U' ⟶ (schemeSpaceFunctor B S hS).obj Z'}
  {pU : U ⟶ (schemeSpaceFunctor B S hS).obj Z} {a : V ⟶ P} {b : U' ⟶ P} {c : U ⟶ V} {d : U ⟶ U'}

variable (E : ThickeningPushoutSpaces i f g h p pV pU' pU a b c d)
  (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom)
include E

section Glue

variable {A : Modules.{u, u} B S hS V.1 V.2} {B' : Modules.{u, u} B S hS U'.1 U'.2}
  (θ : (modulePullback B S hS d).obj B' ⟶ (modulePullback B S hS c).obj A)
  (φ : (modulePushforward B S hS a).obj A ⟶
    (modulePushforward B S hS (c ≫ a)).obj ((modulePullback B S hS c).obj A))
  (ψ : (modulePushforward B S hS b).obj B' ⟶
    (modulePushforward B S hS (c ≫ a)).obj ((modulePullback B S hS c).obj A))

/-- The first projection of the glued module, read on the chart `W_Y` of `V`. -/
def glueFst :
    (pullback φ ψ).val.obj (op dT.U) →ₛₗ[chartDiagramRestrict B S hS a (E.dWY dT)]
      A.val.obj (op (E.WY dT)) :=
  (modulePushforwardCounitAppₛₗ B S hS a A (E.dWY dT)).comp
    ((pullback.fst φ ψ).val.app (op dT.U)).hom

/-- `glueFst` sends a section of the glued module to the counit image of its first projection. -/
theorem glueFst_apply (m : (pullback φ ψ).val.obj (op dT.U)) :
    E.glueFst dT φ ψ m = modulePushforwardCounitApp B S hS a A (E.dWY dT)
      ((pullback.fst φ ψ).val.app (op dT.U) m) :=
  rfl

/-- The second projection of the glued module, read on the chart `W_{Z'}` of `U'`. -/
def glueSnd :
    (pullback φ ψ).val.obj (op dT.U) →ₛₗ[chartDiagramRestrict B S hS b (E.dWZ' dT)]
      B'.val.obj (op (E.WZ' dT)) :=
  (modulePushforwardCounitAppₛₗ B S hS b B' (E.dWZ' dT)).comp
    ((pullback.snd φ ψ).val.app (op dT.U)).hom

/-- `glueSnd` sends a section of the glued module to the counit image of its second projection. -/
theorem glueSnd_apply (m : (pullback φ ψ).val.obj (op dT.U)) :
    E.glueSnd dT φ ψ m = modulePushforwardCounitApp B S hS b B' (E.dWZ' dT)
      ((pullback.snd φ ψ).val.app (op dT.U) m) :=
  rfl

/-- The restriction of `A` to the chart `W_Z` of `U`. -/
abbrev glueα :
    A.val.obj (op (E.WY dT)) →ₛₗ[chartDiagramRestrict B S hS c (E.dWZ dT)]
      ((modulePullback B S hS c).obj A).val.obj (op (E.WZ dT)) :=
  modulePullbackChartSectionₛₗ B S hS c A (E.dWZ dT)

/-- The restriction of `B'` to the chart `W_Z` of `U`, carried to `c^*A` by `θ`. -/
def glueβ :
    B'.val.obj (op (E.WZ' dT)) →ₛₗ[chartDiagramRestrict B S hS d (E.dWZZ' dT)]
      ((modulePullback B S hS c).obj A).val.obj (op (E.WZ dT)) :=
  (θ.val.app (op (E.WZ dT))).hom.comp (modulePullbackChartSectionₛₗ B S hS d B' (E.dWZZ' dT))

/-- `glueβ` sends a section `y` of `B'` over `W_{Z'}` to `θ` applied to its restriction to
`W_Z`. -/
theorem glueβ_apply (y : B'.val.obj (op (E.WZ' dT))) :
    E.glueβ dT θ y = θ.val.app (op (E.WZ dT))
      (modulePullbackChartSection B S hS d B' (E.dWZZ' dT) y) :=
  rfl

variable {θ φ ψ}

/-- The two projections of a section of the glued module agree in `c^*A` over `W_Z`. -/
theorem glue_comm
    (hφ : ∀ x, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ y, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y)))
    (m : (pullback φ ψ).val.obj (op dT.U)) :
    E.glueα dT (E.glueFst dT φ ψ m) = E.glueβ dT θ (E.glueSnd dT φ ψ m) := by
  have hc : φ.val.app (op dT.U) ((pullback.fst φ ψ).val.app (op dT.U) m) =
      ψ.val.app (op dT.U) ((pullback.snd φ ψ).val.app (op dT.U) m) :=
    ((comp_val_app_op _ _ dT.U m).symm.trans
      (congrArg (fun k : pullback φ ψ ⟶ _ => k.val.app (op dT.U) m)
        (pullback.condition (f := φ) (g := ψ)))).trans
      (comp_val_app_op _ _ dT.U m)
  have h1 := (hφ ((pullback.fst φ ψ).val.app (op dT.U) m)).symm
  have h2 := congrArg (modulePushforwardCounitApp B S hS (c ≫ a)
    ((modulePullback B S hS c).obj A) (E.dWZW dT)) hc
  have h3 := hψ ((pullback.snd φ ψ).val.app (op dT.U) m)
  exact h1.trans (h2.trans h3)

/-- A section of the glued module over `W` is determined by its two projections. -/
theorem glue_injective (m₁ m₂ : (pullback φ ψ).val.obj (op dT.U))
    (h₁ : E.glueFst dT φ ψ m₁ = E.glueFst dT φ ψ m₂)
    (h₂ : E.glueSnd dT φ ψ m₁ = E.glueSnd dT φ ψ m₂) : m₁ = m₂ :=
  SheafOfModules.pullback_section_ext φ ψ (op dT.U)
    ((bijective_modulePushforwardCounitApp_smallBaseChangeDiagram a E.rep_a A dT.U).1 h₁)
    ((bijective_modulePushforwardCounitApp_smallBaseChangeDiagram b E.rep_b B' dT.U).1 h₂)

/-- Every section of `A` over `W_Y` is the counit image of a section of `a_*A` over `W`. -/
theorem exists_counitApp_dWY_eq (n : A.val.obj (op (E.WY dT))) :
    ∃ x, modulePushforwardCounitApp B S hS a A (E.dWY dT) x = n :=
  (bijective_modulePushforwardCounitApp_smallBaseChangeDiagram a E.rep_a A dT.U).2 n

/-- Every section of `B'` over `W_{Z'}` is the counit image of a section of `b_*B'` over `W`. -/
theorem exists_counitApp_dWZ'_eq (n' : B'.val.obj (op (E.WZ' dT))) :
    ∃ y, modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y = n' :=
  (bijective_modulePushforwardCounitApp_smallBaseChangeDiagram b E.rep_b B' dT.U).2 n'

/-- Sections `n` of `A` over `W_Y` and `n'` of `B'` over `W_{Z'}` with the same image over `W_Z`,
given as counit images of `x` and `y`, are the projections of a section of the glued module. -/
theorem glue_exists_mk_of
    (hφ : ∀ x, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ y, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y)))
    (n : A.val.obj (op (E.WY dT))) (n' : B'.val.obj (op (E.WZ' dT)))
    (h : E.glueα dT n = E.glueβ dT θ n')
    (x : ((modulePushforward B S hS a).obj A).val.obj (op dT.U))
    (hx : modulePushforwardCounitApp B S hS a A (E.dWY dT) x = n)
    (y : ((modulePushforward B S hS b).obj B').val.obj (op dT.U))
    (hy : modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y = n') :
    ∃ m, E.glueFst dT φ ψ m = n ∧ E.glueSnd dT φ ψ m = n' := by
  have h' : modulePullbackChartSection B S hS c A (E.dWZ dT) n =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT) n') :=
    (modulePullbackChartSectionₛₗ_apply B S hS c A (E.dWZ dT) n).symm.trans
      (h.trans (E.glueβ_apply dT θ n'))
  have hxy : φ.val.app (op dT.U) x = ψ.val.app (op dT.U) y :=
    (E.bijective_counitApp_dWZW dT _).1 ((hφ x).trans
      ((congrArg (modulePullbackChartSection B S hS c A (E.dWZ dT)) hx).trans
        (h'.trans ((congrArg (fun z => θ.val.app (op (E.WZ dT))
          (modulePullbackChartSection B S hS d B' (E.dWZZ' dT) z)) hy).symm.trans
            (hψ y).symm))))
  exact ⟨SheafOfModules.pullbackMk φ ψ (op dT.U) x y hxy,
    (congrArg (modulePushforwardCounitApp B S hS a A (E.dWY dT))
      (SheafOfModules.pullback_fst_pullbackMk φ ψ (op dT.U) x y hxy)).trans hx,
    (congrArg (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT))
      (SheafOfModules.pullback_snd_pullbackMk φ ψ (op dT.U) x y hxy)).trans hy⟩

/-- Sections `n` of `A` over `W_Y` and `n'` of `B'` over `W_{Z'}` with the same image in `c^*A`
over `W_Z` are the two projections of a section of the glued module over `W`. -/
theorem glue_exists_mk
    (hφ : ∀ x, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ y, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y)))
    (n : A.val.obj (op (E.WY dT))) (n' : B'.val.obj (op (E.WZ' dT)))
    (h : E.glueα dT n = E.glueβ dT θ n') :
    ∃ m, E.glueFst dT φ ψ m = n ∧ E.glueSnd dT φ ψ m = n' :=
  (E.exists_counitApp_dWY_eq dT (A := A) n).elim fun x hx =>
    (E.exists_counitApp_dWZ'_eq dT (B' := B') n').elim fun y hy =>
      E.glue_exists_mk_of dT hφ hψ n n' h x hx y hy

/-- **The glued module is, on the chart `W` of `P`, the fibre product of the two pieces.**  Its
sections over `W` are the pairs of sections of `A` over `W_Y` and of `B'` over `W_{Z'}` with the
same image in `c^*A` over `W_Z`. -/
theorem isGlued
    (hφ : ∀ x, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ y, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    MilnorPatching.IsGlued (E.glueα dT) (E.glueβ dT θ) (E.glueFst dT φ ψ) (E.glueSnd dT φ ψ) :=
  ⟨E.glue_comm dT hφ hψ, E.glue_injective dT, E.glue_exists_mk dT hφ hψ⟩

section Affine

variable
    (hU : IsAffine ((SmallEtale.toOver B S hS P.1 ⋙ BigFppfOver.toScheme B S hS).obj dT.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS ((schemeSpaceFunctor B S hS).obj Y').1 ⋙
      BigFppfOver.toScheme B S hS).obj dT.V))

include hU in
/-- The chart `W_Y` of `V` is affine when `W` is. -/
theorem isAffine_WY :
    IsAffine ((SmallEtale.toOver B S hS V.1 ⋙ BigFppfOver.toScheme B S hS).obj (E.WY dT)) :=
  isAffine_smallBaseChange_obj B S hS a E.rep_a E.isAffineHom_a dT.U hU

include hU in
/-- The chart `W_{Z'}` of `U'` is affine when `W` is. -/
theorem isAffine_WZ' :
    IsAffine ((SmallEtale.toOver B S hS U'.1 ⋙ BigFppfOver.toScheme B S hS).obj (E.WZ' dT)) :=
  isAffine_smallBaseChange_obj B S hS b E.rep_b E.isAffineHom_b dT.U hU

include hU in
/-- The chart `W_Z` of `U` is affine when `W` is. -/
theorem isAffine_WZ :
    IsAffine ((SmallEtale.toOver B S hS U.1 ⋙ BigFppfOver.toScheme B S hS).obj (E.WZ dT)) :=
  isAffine_smallBaseChange_obj B S hS c E.rep_c E.isAffineHom_c (E.WY dT) (E.isAffine_WY dT hU)

include hU in
/-- For quasi-coherent `A` and affine `W`, the sections of `c^*A` over `W_Z` are the base change
of the sections of `A` over `W_Y`. -/
theorem isBaseChangeAlong_glueα (hA : A.IsQuasicoherentOnSite) :
    MilnorPatching.IsBaseChangeAlong (chartDiagramRestrict B S hS c (E.dWZ dT))
      (E.glueα dT (A := A)) :=
  isBaseChangeAlong_modulePullbackChartSectionₛₗ B S hS c A hA (E.dWZ dT) (E.isAffine_WZ dT hU)
    (E.isAffine_WY dT hU)

include hU in
/-- For quasi-coherent `B'`, affine `W` and `θ` an isomorphism, the sections of `c^*A` over `W_Z`
are the base change of the sections of `B'` over `W_{Z'}` along `glueβ`. -/
theorem isBaseChangeAlong_glueβ (hB : B'.IsQuasicoherentOnSite) (hθ : IsIso θ) :
    MilnorPatching.IsBaseChangeAlong (chartDiagramRestrict B S hS d (E.dWZZ' dT))
      (E.glueβ dT θ) :=
  (isBaseChangeAlong_modulePullbackChartSectionₛₗ B S hS d B' hB (E.dWZZ' dT)
    (E.isAffine_WZ dT hU) (E.isAffine_WZ' dT hU)).comp_bijective _
    (bijective_val_app_of_isIso_module θ hθ (op (E.WZ dT)))

include hU hV in
/-- **The glued module recovers its two pieces on the charts** (Stacks 08KM): over an affine
chart diagram `W ⟶ T` of `P` over `Y'`, the sections of `A` over `W_Y` and of `B'` over
`W_{Z'}` are the base changes of the sections of the glued module over `W`. -/
theorem isBaseChangeAlong_glueFst_glueSnd (hA : A.IsQuasicoherentOnSite)
    (hB : B'.IsQuasicoherentOnSite) (hθ : IsIso θ)
    (hφ : ∀ x, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ y, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    MilnorPatching.IsBaseChangeAlong (chartDiagramRestrict B S hS a (E.dWY dT))
        (E.glueFst dT φ ψ) ∧
      MilnorPatching.IsBaseChangeAlong (chartDiagramRestrict B S hS b (E.dWZ' dT))
        (E.glueSnd dT φ ψ) :=
  (E.isRelativeSquare dT hU hV).isBaseChangeAlong_of_isGlued (E.isBaseChangeAlong_glueα dT hU hA)
    (E.isBaseChangeAlong_glueβ dT hU (θ := θ) hB hθ) (E.isGlued dT hφ hψ)

include hU hV in
/-- **The glued module of flat pieces is flat on the charts** (Stacks 07RW): over an affine chart
diagram `W ⟶ T` of `P` over `Y'`, the sections of the glued module over `W` are flat over
`Γ(T)` when `A` is flat over `Y` and `B'` over `Z'`. -/
theorem flat_glue_sections (hA : A.IsQuasicoherentOnSite) (hB : B'.IsQuasicoherentOnSite)
    (hθ : IsIso θ)
    (hAf : IsFlatOver B S hS V.2 pV.hom A) (hBf : IsFlatOver B S hS U'.2 pU'.hom B')
    (hφ : ∀ x, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ y, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    @Module.Flat (chartRing B S hS ((schemeSpaceFunctor B S hS).obj Y').1
        ((schemeSpaceFunctor B S hS).obj Y').2 dT.V) ((pullback φ ψ).val.obj (op dT.U)) _ _
      (Module.compHom _ (chartDiagramRestrict B S hS p dT)) := by
  have hTY := isAffine_smallBaseChange_obj B S hS _ E.rep_h E.isAffineHom_sp_h dT.V hV
  have hTZ' := isAffine_smallBaseChange_obj B S hS _ E.rep_g E.isAffineHom_sp_g dT.V hV
  exact (E.isRelativeSquare dT hU hV).flat_of_isGlued (E.isBaseChangeAlong_glueα dT hU hA)
    (E.isBaseChangeAlong_glueβ dT hU (θ := θ) hB hθ) (E.isGlued dT hφ hψ)
    (flat_sections_of_isFlatOver_chartDiagram B S hS pV A hA hAf (E.dWYT dT)
      (E.isAffine_WY dT hU) hTY)
    (flat_sections_of_isFlatOver_chartDiagram B S hS pU' B' hB hBf (E.dWZ'T dT)
      (E.isAffine_WZ' dT hU) hTZ')

end Affine

end Glue

end ThickeningPushoutSpaces

end AlgebraicGeometry.Space

end
