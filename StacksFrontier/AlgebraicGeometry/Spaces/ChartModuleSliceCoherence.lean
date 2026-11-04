module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleGlueingEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartDictionaryCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction
public import StacksFrontier.CategoryTheory.Adjunction.UnitSectionProjection

/-!
# The first dictionary square of Stacks 03LY

Stacks 03LY describes a sheaf of `𝒪_X`-modules on the small étale site of an algebraic space `X`
by a family of modules on the small étale sites of the étale scheme charts of `X`, while the
glueing description available for an arbitrary site carries a module on each slice `X_étale/U`.
`StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison` identifies the two indexings
of the chartwise pullback object by object, through
`AlgebraicGeometry.Space.chartModuleInverseImageSliceIso`; this file proves that for a *morphism
of charts* the identification is compatible with the two composition isomorphisms.

It is the module-level companion of
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso_comp`, and the assembly is the
same: the chart-level bridge of Stacks 03LU against Stacks 03LW, the coherence of the
restriction-along-equal-functors half, and the naturality of the comparison of Stacks 03LW,
joined by `CategoryTheory.comp_bridge_rearrange`.

## Main results

* `AlgebraicGeometry.Space.chartModuleSliceTail`: the restriction-along-equal-functors half of
  the module dictionary, that is the factors of
  `AlgebraicGeometry.Space.chartModuleInverseImageSliceIso` that follow the comparison of
  Stacks 03LW, and `AlgebraicGeometry.Space.chartModuleSliceTail_hom_app_val_app`: that half on
  sections.
* `AlgebraicGeometry.Space.chartModuleSliceTail_comp`: the half is compatible with the
  composition isomorphisms on the two sides — the module-level form of
  `AlgebraicGeometry.Space.chartLocalizationPostcompIso_comp`.
* `AlgebraicGeometry.Space.chartModuleSliceBridge`: the chart-level bridge of Stacks 03LU
  against Stacks 03LW for two composable morphisms of charts.
* `AlgebraicGeometry.Space.chartModuleInverseImageSliceApp_comp`: **the first dictionary square
  of Stacks 03LY** for a morphism of charts, which is the identity stated by
  `AlgebraicGeometry.Space.ChartModuleInverseImageSliceSquare`, written out as a `∀` so that a
  consumer can take it in a binder.
* **The cocycle condition of Stacks 03LY for the chartwise reading of a slice-indexed glueing
  datum for modules** — that square handed to
  `AlgebraicGeometry.Space.isChartModuleCocycle_sliceToChartModuleTransitionFamily_of_square`,
  which is
  `isChartModuleCocycle_sliceToChartModuleTransitionFamily_of_etaleRestriction` below.

## Implementation notes

Every factor of `AlgebraicGeometry.Space.chartModuleSliceTail` is restriction of modules along
an isomorphism of functors of sites or a transport of the structure map, so on sections it is
either the identity or the module restricted along the component of
`AlgebraicGeometry.Space.chartLocalizationPostcompIso`; the coherence of the half is therefore
the site-level identity
`AlgebraicGeometry.Space.chartLocalizationPostcompIso_comp_inv_app_op` read through the module,
and no further input is needed.

Three measurements shape everything below.

* A section of a pushforward of sheaves of modules may be presented to the elaborator in the
  two spellings — through the pushforward and through the module it is pushed forward from —
  only *one step at a time*: asked for two steps at once the unifier exhausts the heartbeat
  limit.  Every such identification is therefore a named one-step abbreviation
  (`AlgebraicGeometry.Space.etaleModulePullbackSect` and the five like it), and the sectionwise
  statements below are written with those abbreviations rather than with the spelling the
  surrounding term happens to carry.
* For the same reason the five factors of the half are named separately: the half is unfolded on
  sections one factor at a time, each factor by its own definitional step, and never in one
  `CategoryTheory.Iso.trans` chain.
* The composite `chartMap g ≫ chartMap f` is never presented as `chartMap (g ≫ f)` through the
  composite of the two étale restrictions: that identification needs the strictness of the
  Stacks 03LP tower *and* `AlgebraicGeometry.Space.chartMap_comp` at once.  Instead the
  comparison `AlgebraicGeometry.Space.etaleModulePullbackComp` is carried explicitly, and the
  two identifications are taken separately
  (`AlgebraicGeometry.Space.chartModuleSliceCompSectPostcomp` and
  `AlgebraicGeometry.Space.chartModuleSliceCompSectChartMap`).

## References

* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace SheafOfModules

universe v' u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- Two morphisms of sheaves of modules that agree on sections are equal. -/
theorem hom_ext_val_app {M N : SheafOfModules.{v'} R} {φ ψ : M ⟶ N}
    (h : ∀ (A : Cᵒᵖ) (x : M.val.obj A), φ.val.app A x = ψ.val.app A x) : φ = ψ :=
  SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun A ↦ ModuleCat.hom_ext (LinearMap.ext (h A)))

/-- A morphism of sheaves of modules applied to equal sections. -/
theorem val_app_congr {N P : SheafOfModules.{v'} R} (ψ : N ⟶ P) (A : Cᵒᵖ)
    {y y' : N.val.obj A} (h : y = y') : ψ.val.app A y = ψ.val.app A y' :=
  Stacks.CategoryTheory.proj_congr h _

/-- A composite of morphisms of sheaves of modules on a section whose first image is known. -/
private theorem comp_val_app_eq {M N P : SheafOfModules.{v'} R} (φ : M ⟶ N) (ψ : N ⟶ P)
    (A : Cᵒᵖ) {x : M.val.obj A} {y : N.val.obj A} (h : φ.val.app A x = y) :
    (φ ≫ ψ).val.app A x = ψ.val.app A y :=
  val_app_congr ψ A h

end SheafOfModules

namespace CategoryTheory

/-- The rearrangement that turns a naturality square, a bridge identity, a coherence identity
and a splitting into one identity of fourfold composites.  Every morphism is implicit and
determined by the four hypotheses, so an application performs no search: the conclusion is
checked against the goal once, factor by factor.  This is
`CategoryTheory.comp_bridge_rearrange` with the comparison that the coherence identity carries
split off as `i`, which is the shape the module dictionary presents. -/
theorem comp_bridge_rearrange_split {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ Bo P Q R : C} {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄}
    {c₁ : A₁ ⟶ Bo} {b₁ : Bo ⟶ A₃} {p : A₀ ⟶ P} {q : P ⟶ Q} {e : Q ⟶ Bo} {i : Bo ⟶ Q}
    {r : Q ⟶ R} {w : R ⟶ A₄} (hnat : b ≫ c = c₁ ≫ b₁) (hbr : a ≫ c₁ = p ≫ q ≫ e)
    (hcps : b₁ ≫ d = (i ≫ r) ≫ w) (hei : e ≫ i = 𝟙 Q) :
    (a ≫ b) ≫ c ≫ d = p ≫ (q ≫ r) ≫ w := by
  simp only [Category.assoc]
  rw [← Category.assoc b, hnat]
  simp only [Category.assoc]
  rw [← Category.assoc a, hbr]
  simp only [Category.assoc]
  rw [hcps]
  simp only [Category.assoc]
  rw [← Category.assoc e, hei, Category.id_comp]

/-- The rearrangement that moves a split morphism across a bridge identity: if `u ≫ v ≫ i` is
`p ≫ q` and `i` is split by `j`, then `u ≫ v` is `p ≫ q ≫ j`.  Stated abstractly, with every
morphism positional, because the terms it is applied to are large and spelled inconsistently. -/
theorem comp_bridge_uncancel {C : Type*} [Category C] {A₀ A₁ A₂ A₃ P : C} (u : A₀ ⟶ A₁)
    (v : A₁ ⟶ A₂) (i : A₂ ⟶ A₃) (j : A₃ ⟶ A₂) (p : A₀ ⟶ P) (q : P ⟶ A₃)
    (hij : i ≫ j = 𝟙 A₂) (h : u ≫ v ≫ i = p ≫ q) :
    u ≫ v = p ≫ q ≫ j := by
  have h1 : p ≫ q ≫ j = (p ≫ q) ≫ j := (Category.assoc _ _ _).symm
  have h2 : (p ≫ q) ≫ j = (u ≫ v ≫ i) ≫ j :=
    Stacks.CategoryTheory.proj_congr h.symm (fun z ↦ z ≫ j)
  have h3 : (u ≫ v ≫ i) ≫ j = u ≫ v ≫ i ≫ j := by
    rw [Category.assoc, Category.assoc]
  have h4 : u ≫ v ≫ i ≫ j = u ≫ v := by rw [hij, Category.comp_id]
  exact ((h1.trans h2).trans (h3.trans h4)).symm

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Sections of the restrictions -/

section Sections

/-- Sections of an étale pullback of modules over a chart of the source, read as sections of the
module over the composite chart of the target. -/
noncomputable def etaleModulePullbackSect {D' A' : AlgebraicSpaces B S hS} (h : D' ⟶ A')
    (hh : IsEtale B S hS h.hom) (N : Modules.{u, u} B S hS A'.1 A'.2)
    (a : (SmallEtale B S hS D'.1)ᵒᵖ)
    (x : (((etaleModulePullback.{u, u} B S hS h hh).obj N).val.obj a)) :
    N.val.obj (op ((smallEtalePostcomp B S hS h hh).obj a.unop)) := x

/-- `AlgebraicGeometry.Space.etaleModulePullbackSect` read in the other direction. -/
noncomputable def etaleModulePullbackSectInv {D' A' : AlgebraicSpaces B S hS} (h : D' ⟶ A')
    (hh : IsEtale B S hS h.hom) (N : Modules.{u, u} B S hS A'.1 A'.2)
    (a : (SmallEtale B S hS D'.1)ᵒᵖ)
    (y : N.val.obj (op ((smallEtalePostcomp B S hS h hh).obj a.unop))) :
    (((etaleModulePullback.{u, u} B S hS h hh).obj N).val.obj a) := y


end Sections

/-! ### The restriction-along-equal-functors half -/

section Tail

variable {V U : SmallEtale B S hS X.1} (f : V ⟶ U)

/-- The first factor of the restriction-along-equal-functors half: restriction to the slice at
the larger chart followed by étale restriction along the morphism of charts is restriction along
the composite functor of sites. -/
noncomputable def chartModuleSliceTailFactorOne :=
  @SheafOfModules.pushforwardComp
      (SmallEtale B S hS (chartSpace B S hS X V).1) _
      (SmallEtale B S hS (chartSpace B S hS X U).1) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f))
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      (structureRingSheaf B S hS (chartSpace B S hS X U)) inferInstance
      (chartMapRingMap B S hS X f)
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.chartLocalization B S hS X.1 U)
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_chartLocalization_chartSpace B S hS X U)
      (chartSliceRingMap B S hS X U)

/-- The second factor: the composite structure map of that two-step restriction is the
identity. -/
noncomputable def chartModuleSliceTailFactorTwo :=
  @SheafOfModules.pushforwardCongr
      (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U)
      (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
        SmallEtale.chartLocalization B S hS X.1 U)
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_smallEtalePostcomp_comp_chartLocalization B S hS X f) _ _
      (chartMapRingMap_comp B S hS X f)

/-- The third factor: the comparison of Stacks 04M0 identifies postcomposition followed by the
comparison at the larger chart with the comparison at the smaller chart followed by the slice
functor, and carries one structure map to the other. -/
noncomputable def chartModuleSliceTailFactorThree :=
  @SheafOfModules.pushforwardCongr₂
      (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)
      (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
        SmallEtale.chartLocalization B S hS X.1 U)
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_chartLocalization_comp_overMap B S hS X f)
      (isContinuous_smallEtalePostcomp_comp_chartLocalization B S hS X f)
      (chartPostcompRingMap B S hS X f) _ (chartLocalizationPostcompIso B S hS X f).symm
      (chartPostcompRingMap_natTrans B S hS X f)

/-- The fourth factor: the composite structure map of the slice pullback after the comparison of
Stacks 04M0 is the identity. -/
noncomputable def chartModuleSliceTailFactorFour :=
  (@SheafOfModules.pushforwardCongr
      (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_chartLocalization_comp_overMap B S hS X f) _ _
      (chartOverMapRingMap_comp B S hS X f)).symm

/-- The fifth factor: restriction along the comparison at the smaller chart followed by the
slice functor is restriction to the slice at the smaller chart after the slice pullback. -/
noncomputable def chartModuleSliceTailFactorFive :=
  (@SheafOfModules.pushforwardComp
      (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over V) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over V)
      (SmallEtale.chartLocalization B S hS X.1 V)
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      ((structureRingSheaf B S hS X).over V)
      (isContinuous_chartLocalization_chartSpace B S hS X V)
      (chartSliceRingMap B S hS X V)
      ((SmallEtale.topology B S hS X.1).over U) (Over.map f)
      ((structureRingSheaf B S hS X).over U) inferInstance
      (Sheaf.pushforwardOverMapIso (structureRingSheaf B S hS X) f).inv).symm

/-- The last two factors of the half. -/
noncomputable def chartModuleSliceTailSuffixFour :=
  chartModuleSliceTailFactorFour B S hS X f ≪≫ chartModuleSliceTailFactorFive B S hS X f

/-- The last three factors of the half. -/
noncomputable def chartModuleSliceTailSuffixThree :=
  chartModuleSliceTailFactorThree B S hS X f ≪≫ chartModuleSliceTailSuffixFour B S hS X f

/-- The last four factors of the half. -/
noncomputable def chartModuleSliceTailSuffixTwo :=
  chartModuleSliceTailFactorTwo B S hS X f ≪≫ chartModuleSliceTailSuffixThree B S hS X f

/-- **The restriction-along-equal-functors half of the module dictionary for a morphism of
charts**: the factors of `AlgebraicGeometry.Space.chartModuleInverseImageSliceIso` that follow
the comparison of Stacks 03LW. -/
noncomputable def chartModuleSliceTail :
    chartModuleSliceReindex B S hS X U ⋙
        etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f) ≅
      SheafOfModules.overMap (structureRingSheaf B S hS X) f ⋙
        chartModuleSliceReindex B S hS X V :=
  chartModuleSliceTailFactorOne B S hS X f ≪≫ chartModuleSliceTailSuffixTwo B S hS X f

/-- **The module dictionary for a morphism of charts is the comparison of Stacks 03LW followed
by `AlgebraicGeometry.Space.chartModuleSliceTail`.**  This is how
`AlgebraicGeometry.Space.chartModuleInverseImageSliceIso` is built, with the two halves
named. -/
theorem chartModuleInverseImageSliceIso_eq :
    chartModuleInverseImageSliceIso B S hS X f =
      Functor.isoWhiskerLeft (chartModuleSliceReindex B S hS X U)
          (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
            (isEtale_chartMap B S hS X f)) ≪≫
        chartModuleSliceTail B S hS X f :=
  rfl

variable (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U))
    (A : (SmallEtale B S hS (chartSpace B S hS X V).1)ᵒᵖ)

/-- Sections of the two-step restriction to the slice at the larger chart, read as sections of
the module over the composite chart of the slice.  The two readings are definitionally equal;
naming the identification keeps every application of a restriction map of the module to such a
section a first-order match. -/
noncomputable def chartModuleSliceTailSect
    (x : (((chartModuleSliceReindex B S hS X U ⋙
      etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).obj T).val.obj A)) :
    T.val.obj (op ((SmallEtale.chartLocalization B S hS X.1 U).obj
      ((smallEtalePostcomp B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).obj A.unop))) := x

/-- The first factor of the half is the identity on sections. -/
theorem chartModuleSliceTailFactorOne_val_app
    (x : (((chartModuleSliceReindex B S hS X U ⋙
      etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).obj T).val.obj A)) :
    ((chartModuleSliceTailFactorOne B S hS X f).hom.app T).val.app A x = x := rfl

/-- The second factor of the half is the identity on sections. -/
theorem chartModuleSliceTailFactorTwo_val_app
    (x : (((chartModuleSliceReindex B S hS X U ⋙
      etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).obj T).val.obj A)) :
    ((chartModuleSliceTailFactorTwo B S hS X f).hom.app T).val.app A x = x := rfl

/-- The third factor of the half, on sections: the module restricted along the component of the
comparison of Stacks 04M0. -/
theorem chartModuleSliceTailFactorThree_val_app
    (x : (((chartModuleSliceReindex B S hS X U ⋙
      etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).obj T).val.obj A)) :
    ((chartModuleSliceTailFactorThree B S hS X f).hom.app T).val.app A x =
      T.val.map ((chartLocalizationPostcompIso B S hS X f).inv.app A.unop).op
        (chartModuleSliceTailSect B S hS X f T A x) := rfl

/-- The last two factors of the half are the identity on sections. -/
theorem chartModuleSliceTailSuffixFour_val_app :
    ∀ y, ((chartModuleSliceTailSuffixFour B S hS X f).hom.app T).val.app A y = y :=
  fun _ ↦ rfl

/-- **Sections of the restriction-along-equal-functors half.**  Every factor is the identity on
sections except the one induced by `AlgebraicGeometry.Space.chartLocalizationPostcompIso`, so
the half is the module restricted along the component of that comparison. -/
theorem chartModuleSliceTail_hom_app_val_app
    (x : (((chartModuleSliceReindex B S hS X U ⋙
      etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).obj T).val.obj A)) :
    ((chartModuleSliceTail B S hS X f).hom.app T).val.app A x =
      T.val.map ((chartLocalizationPostcompIso B S hS X f).inv.app A.unop).op
        (chartModuleSliceTailSect B S hS X f T A x) := by
  refine (SheafOfModules.comp_val_app_eq _ _ A
    (chartModuleSliceTailFactorOne_val_app B S hS X f T A x)).trans ?_
  refine (SheafOfModules.comp_val_app_eq _ _ A
    (chartModuleSliceTailFactorTwo_val_app B S hS X f T A x)).trans ?_
  refine (SheafOfModules.comp_val_app_eq _ _ A
    (chartModuleSliceTailFactorThree_val_app B S hS X f T A x)).trans ?_
  exact chartModuleSliceTailSuffixFour_val_app B S hS X f T A _


end Tail

/-! ### The comparisons at a module, with the endpoints written out -/

/-- The restriction-along-equal-functors half at a module on the slice, with both endpoints
written out uncomposed.  The reconciliation of `(F ⋙ G).obj T` with `G.obj (F.obj T)` happens
here, once, at a variable `T`. -/
def chartModuleSliceTailApp {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    (etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).obj ((chartModuleSliceReindex B S hS X U).obj T) ⟶
      (chartModuleSliceReindex B S hS X V).obj
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) :=
  (chartModuleSliceTail B S hS X f).hom.app T

/-- The strict composition of the étale restrictions at a module, with both endpoints written
out uncomposed. -/
def etaleModulePullbackCompApp {A' C' D' : AlgebraicSpaces B S hS} (h : D' ⟶ A') (g' : A' ⟶ C')
    (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g'.hom)
    (hhg : IsEtale B S hS (h ≫ g').hom) (M : Modules.{u, u} B S hS C'.1 C'.2) :
    (etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g' hg).obj M) ⟶
      (etaleModulePullback.{u, u} B S hS (h ≫ g') hhg).obj M :=
  (etaleModulePullbackComp B S hS h g' hh hg hhg).hom.app M

/-- `AlgebraicGeometry.Space.etaleModulePullbackCompApp` read backwards. -/
def etaleModulePullbackCompInvApp {A' C' D' : AlgebraicSpaces B S hS} (h : D' ⟶ A')
    (g' : A' ⟶ C') (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g'.hom)
    (hhg : IsEtale B S hS (h ≫ g').hom) (M : Modules.{u, u} B S hS C'.1 C'.2) :
    (etaleModulePullback.{u, u} B S hS (h ≫ g') hhg).obj M ⟶
      (etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g' hg).obj M) :=
  (etaleModulePullbackComp B S hS h g' hh hg hhg).inv.app M

/-- The two readings of the strict composition of étale restrictions cancel. -/
theorem etaleModulePullbackCompInvApp_comp_hom {A' C' D' : AlgebraicSpaces B S hS} (h : D' ⟶ A')
    (g' : A' ⟶ C') (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g'.hom)
    (hhg : IsEtale B S hS (h ≫ g').hom) (M : Modules.{u, u} B S hS C'.1 C'.2) :
    etaleModulePullbackCompInvApp B S hS h g' hh hg hhg M ≫
        etaleModulePullbackCompApp B S hS h g' hh hg hhg M = 𝟙 _ :=
  (etaleModulePullbackComp B S hS h g' hh hg hhg).inv_hom_id_app M

/-- The two readings of the strict composition of étale restrictions cancel, the other way. -/
theorem etaleModulePullbackCompApp_comp_inv {A' C' D' : AlgebraicSpaces B S hS} (h : D' ⟶ A')
    (g' : A' ⟶ C') (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g'.hom)
    (hhg : IsEtale B S hS (h ≫ g').hom) (M : Modules.{u, u} B S hS C'.1 C'.2) :
    etaleModulePullbackCompApp B S hS h g' hh hg hhg M ≫
        etaleModulePullbackCompInvApp B S hS h g' hh hg hhg M = 𝟙 _ :=
  (etaleModulePullbackComp B S hS h g' hh hg hhg).hom_inv_id_app M

/-- The dictionary at a module is the comparison of Stacks 03LW followed by the
restriction-along-equal-functors half. -/
theorem chartModuleInverseImageSliceApp_eq {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    chartModuleInverseImageSliceApp B S hS X f T =
      (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
            (isEtale_chartMap B S hS X f)).hom.app
          ((chartModuleSliceReindex B S hS X U).obj T) ≫
        chartModuleSliceTailApp B S hS X f T :=
  rfl

/-! ### The coherence of the half -/

section Comp

variable {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V)
    (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U))
    (A : (SmallEtale B S hS (chartSpace B S hS X W).1)ᵒᵖ)

/-- Sections of the twofold restriction along two morphisms of charts, read as sections of the
module over the twice-composite chart of the slice. -/
noncomputable def chartModuleSliceCompSect
    (x : (((etaleModulePullback.{u, u} B S hS (chartMap B S hS X g)
        (isEtale_chartMap B S hS X g)).obj
      ((chartModuleSliceReindex B S hS X U ⋙
        etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).obj T)).val.obj A)) :
    T.val.obj (op ((SmallEtale.chartLocalization B S hS X.1 U).obj
      ((smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f)).obj
        ((smallEtalePostcomp B S hS (chartMap B S hS X g)
          (isEtale_chartMap B S hS X g)).obj A.unop)))) :=
  chartModuleSliceTailSect B S hS X f T
    (op ((smallEtalePostcomp B S hS (chartMap B S hS X g)
      (isEtale_chartMap B S hS X g)).obj A.unop))
    (etaleModulePullbackSect B S hS (chartMap B S hS X g) (isEtale_chartMap B S hS X g) _ A x)

/-- The twice-composite chart of the slice, read through the composite of the two chartwise
postcompositions.  This is strictness of the Stacks 03LP tower, which is definitional. -/
noncomputable def chartModuleSliceCompSectPostcomp
    (z : T.val.obj (op ((SmallEtale.chartLocalization B S hS X.1 U).obj
      ((smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f)).obj
        ((smallEtalePostcomp B S hS (chartMap B S hS X g)
          (isEtale_chartMap B S hS X g)).obj A.unop))))) :
    T.val.obj (op ((SmallEtale.chartLocalization B S hS X.1 U).obj
      ((smallEtalePostcomp B S hS (chartMap B S hS X g ≫ chartMap B S hS X f)
        (isEtale_chartMap_comp B S hS X f g)).obj A.unop))) := z

/-- The composite of the two represented morphisms of charts, read as the represented morphism
of the composite morphism of charts.  This is
`AlgebraicGeometry.Space.chartMap_comp`, which is definitional. -/
noncomputable def chartModuleSliceCompSectChartMap
    (z : T.val.obj (op ((SmallEtale.chartLocalization B S hS X.1 U).obj
      ((smallEtalePostcomp B S hS (chartMap B S hS X g ≫ chartMap B S hS X f)
        (isEtale_chartMap_comp B S hS X f g)).obj A.unop)))) :
    T.val.obj (op ((SmallEtale.chartLocalization B S hS X.1 U).obj
      ((smallEtalePostcomp B S hS (chartMap B S hS X (g ≫ f))
        (isEtale_chartMap B S hS X (g ≫ f))).obj A.unop))) := z

/-- Sections of a slice pullback of modules, read as sections of the module over the image
object of the slice. -/
noncomputable def overMapSect {V' U' : SmallEtale B S hS X.1} (f' : V' ⟶ U')
    (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U')) (b : Over V')
    (z : (((SheafOfModules.overMap (structureRingSheaf B S hS X) f').obj M).val.obj (op b))) :
    M.val.obj (op ((Over.map f').obj b)) := z

/-- overMap_val_map_postcompIso_inv: the T'-to-T conversion -/
theorem overMap_val_map_postcompIso_inv
    (w : (((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj
    T).val.obj (op ((SmallEtale.chartLocalization B S hS X.1 V).obj
      ((smallEtalePostcomp B S hS (chartMap B S hS X g)
        (isEtale_chartMap B S hS X g)).obj A.unop))))) :
    ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T).val.map
        ((chartLocalizationPostcompIso B S hS X g).inv.app A.unop).op w =
      T.val.map ((Over.map f).map
          ((chartLocalizationPostcompIso B S hS X g).inv.app A.unop)).op
        (overMapSect B S hS X f T _ w) := rfl

/-- Sections of the module over a chart of the slice, read as sections of the reindexing. -/
noncomputable def chartModuleSliceReindexSectInv (U' : SmallEtale B S hS X.1)
    (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U'))
    (a : (SmallEtale B S hS (chartSpace B S hS X U').1)ᵒᵖ)
    (z : M.val.obj (op ((SmallEtale.chartLocalization B S hS X.1 U').obj a.unop))) :
    (((chartModuleSliceReindex B S hS X U').obj M).val.obj a) := z

/-- `AlgebraicGeometry.Space.overMapSect` read in the other direction. -/
noncomputable def overMapSectInv {V' U' : SmallEtale B S hS X.1} (f' : V' ⟶ U')
    (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U')) (b : Over V')
    (z : M.val.obj (op ((Over.map f').obj b))) :
    (((SheafOfModules.overMap (structureRingSheaf B S hS X) f').obj M).val.obj (op b)) := z

/-- The two-step reading of the half on sections, assembled: the module restricted along the
component of the comparison of Stacks 04M0 at the larger chart, then along the slice pullback of
the component at the smaller chart, is the module restricted along the composite. -/
theorem chartModuleSliceTailCompSect
    (z : T.val.obj (op ((SmallEtale.chartLocalization B S hS X.1 U).obj
    ((smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f)).obj
      ((smallEtalePostcomp B S hS (chartMap B S hS X g)
        (isEtale_chartMap B S hS X g)).obj A.unop))))) :
    ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T).val.map
        ((chartLocalizationPostcompIso B S hS X g).inv.app A.unop).op
      (overMapSectInv B S hS X f T
        ((SmallEtale.chartLocalization B S hS X.1 V).obj
          ((smallEtalePostcomp B S hS (chartMap B S hS X g)
            (isEtale_chartMap B S hS X g)).obj A.unop))
        (T.val.map ((chartLocalizationPostcompIso B S hS X f).inv.app
          ((smallEtalePostcomp B S hS (chartMap B S hS X g)
            (isEtale_chartMap B S hS X g)).obj A.unop)).op z)) =
      T.val.map (((chartLocalizationPostcompIso B S hS X f).inv.app
            ((smallEtalePostcomp B S hS (chartMap B S hS X g)
              (isEtale_chartMap B S hS X g)).obj A.unop)).op ≫
          ((Over.map f).map
            ((chartLocalizationPostcompIso B S hS X g).inv.app A.unop)).op) z := by
  refine Eq.trans (overMap_val_map_postcompIso_inv B S hS X f g T A _) ?_
  exact (PresheafOfModules.map_comp_apply T.val
    (((chartLocalizationPostcompIso B S hS X f).inv.app
      ((smallEtalePostcomp B S hS (chartMap B S hS X g)
        (isEtale_chartMap B S hS X g)).obj A.unop)).op)
    (((Over.map f).map ((chartLocalizationPostcompIso B S hS X g).inv.app A.unop)).op) z).symm

/-- The composition comparison of the slice pullbacks, on sections: it is the module restricted
along the component of `CategoryTheory.Over.mapComp`. -/
theorem overMapComp_inv_val_app_sect
    (v : T.val.obj (op ((Over.map (g ≫ f)).obj
    ((SmallEtale.chartLocalization B S hS X.1 W).obj A.unop)))) :
    ((chartModuleSliceReindex B S hS X W).map
          ((CategoryTheory.SiteGlueing.overMapComp (structureRingSheaf B S hS X) f
            g).inv.app T)).val.app A
        (chartModuleSliceReindexSectInv B S hS X W
          ((SheafOfModules.overMap (structureRingSheaf B S hS X) (g ≫ f)).obj T) A
          (overMapSectInv B S hS X (g ≫ f) T
            ((SmallEtale.chartLocalization B S hS X.1 W).obj A.unop) v)) =
      chartModuleSliceReindexSectInv B S hS X W
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).obj
          ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T)) A
        (overMapSectInv B S hS X g
          ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T)
          ((SmallEtale.chartLocalization B S hS X.1 W).obj A.unop)
          (T.val.map ((Over.mapComp g f).inv.app
            ((SmallEtale.chartLocalization B S hS X.1 W).obj A.unop)).op v)) := rfl

/-- Sections of the twofold restriction, read as sections of the restriction along the
represented morphism of the composite morphism of charts. -/
noncomputable def chartModuleSliceCompSectComp
    (x : (((etaleModulePullback.{u, u} B S hS (chartMap B S hS X g)
        (isEtale_chartMap B S hS X g)).obj
      ((chartModuleSliceReindex B S hS X U ⋙
        etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).obj T)).val.obj A)) :
    (((chartModuleSliceReindex B S hS X U ⋙
      etaleModulePullback.{u, u} B S hS (chartMap B S hS X (g ≫ f))
        (isEtale_chartMap B S hS X (g ≫ f))).obj T).val.obj A) :=
  etaleModulePullbackSectInv B S hS (chartMap B S hS X (g ≫ f)) (isEtale_chartMap B S hS X (g ≫ f))
    ((chartModuleSliceReindex B S hS X U).obj T) A
    (chartModuleSliceReindexSectInv B S hS X U T
      (op ((smallEtalePostcomp B S hS (chartMap B S hS X (g ≫ f))
        (isEtale_chartMap B S hS X (g ≫ f))).obj A.unop))
      (chartModuleSliceCompSectChartMap B S hS X f g T A
        (chartModuleSliceCompSectPostcomp B S hS X f g T A
          (chartModuleSliceCompSect B S hS X f g T A x))))

/-- **The restriction-along-equal-functors half of the module dictionary is compatible with the
composition isomorphisms.**  This is the module-level form of
`AlgebraicGeometry.Space.chartLocalizationPostcompIso_comp`: on sections every isomorphism
involved is the module restricted along a component of the comparison of Stacks 04M0 or of
`CategoryTheory.Over.mapComp`, so the identity is the site-level one read through the module.

The strict composition `AlgebraicGeometry.Space.etaleModulePullbackComp` of the étale
restrictions is carried explicitly on the right, so that the composite of the two chartwise
postcompositions is never presented as the postcomposition along the represented morphism of the
composite morphism of charts. -/
theorem chartModuleSliceTail_comp :
    (etaleModulePullback.{u, u} B S hS (chartMap B S hS X g)
            (isEtale_chartMap B S hS X g)).map (chartModuleSliceTailApp B S hS X f T) ≫
        chartModuleSliceTailApp B S hS X g
          ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) =
      (etaleModulePullbackCompApp B S hS (chartMap B S hS X g) (chartMap B S hS X f)
              (isEtale_chartMap B S hS X g) (isEtale_chartMap B S hS X f)
              (isEtale_chartMap_comp B S hS X f g)
            ((chartModuleSliceReindex B S hS X U).obj T) ≫
          chartModuleSliceTailApp B S hS X (g ≫ f) T) ≫
        (chartModuleSliceReindex B S hS X W).map (overMapCompInvApp B S hS X f g T) := by
  refine SheafOfModules.hom_ext_val_app fun A x ↦ ?_
  let F := fun z ↦ chartModuleSliceReindexSectInv B S hS X W
    ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).obj
      ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T)) A
    (overMapSectInv B S hS X g
      ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T)
      ((SmallEtale.chartLocalization B S hS X.1 W).obj A.unop) z)
  refine Eq.trans (Eq.refl
    (((chartModuleSliceTail B S hS X g).hom.app
          ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T)).val.app A
      (etaleModulePullbackSectInv B S hS (chartMap B S hS X g) (isEtale_chartMap B S hS X g) _ A
        (((chartModuleSliceTail B S hS X f).hom.app T).val.app
          (op ((smallEtalePostcomp B S hS (chartMap B S hS X g)
            (isEtale_chartMap B S hS X g)).obj A.unop))
          (etaleModulePullbackSect B S hS (chartMap B S hS X g)
            (isEtale_chartMap B S hS X g) _ A x))))) ?_
  refine Eq.trans (Stacks.CategoryTheory.proj_congr
    (chartModuleSliceTail_hom_app_val_app B S hS X f T
      (op ((smallEtalePostcomp B S hS (chartMap B S hS X g)
        (isEtale_chartMap B S hS X g)).obj A.unop))
      (etaleModulePullbackSect B S hS (chartMap B S hS X g) (isEtale_chartMap B S hS X g) _ A x))
    (fun z ↦ ((chartModuleSliceTail B S hS X g).hom.app
          ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T)).val.app A
        (etaleModulePullbackSectInv B S hS (chartMap B S hS X g)
          (isEtale_chartMap B S hS X g) _ A z))) ?_
  refine Eq.trans (chartModuleSliceTail_hom_app_val_app B S hS X g
    ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) A _) ?_
  refine Eq.trans (Stacks.CategoryTheory.proj_congr
    (chartModuleSliceTailCompSect B S hS X f g T A (chartModuleSliceCompSect B S hS X f g T A x))
    F) ?_
  refine Eq.trans (Stacks.CategoryTheory.proj_congr
    (T.val.congr_map_apply
      (chartLocalizationPostcompIso_comp_inv_app_op B S hS X f g A.unop)
      (chartModuleSliceCompSect B S hS X f g T A x))
    F) ?_
  refine Eq.symm ?_
  refine Eq.trans (Eq.refl
    (((chartModuleSliceReindex B S hS X W).map
          ((CategoryTheory.SiteGlueing.overMapComp (structureRingSheaf B S hS X) f
            g).inv.app T)).val.app A
      (((chartModuleSliceTail B S hS X (g ≫ f)).hom.app T).val.app A
        (chartModuleSliceCompSectComp B S hS X f g T A x)))) ?_
  refine Eq.trans (Stacks.CategoryTheory.proj_congr
    (chartModuleSliceTail_hom_app_val_app B S hS X (g ≫ f) T A
      (chartModuleSliceCompSectComp B S hS X f g T A x))
    (fun z ↦ ((chartModuleSliceReindex B S hS X W).map
        ((CategoryTheory.SiteGlueing.overMapComp (structureRingSheaf B S hS X) f
          g).inv.app T)).val.app A z)) ?_
  refine Eq.trans (overMapComp_inv_val_app_sect B S hS X f g T A _) ?_
  exact Stacks.CategoryTheory.proj_congr
    (PresheafOfModules.map_comp_apply T.val
      (((chartLocalizationPostcompIso B S hS X (g ≫ f)).inv.app A.unop).op)
      (((Over.mapComp g f).inv.app
        ((SmallEtale.chartLocalization B S hS X.1 W).obj A.unop)).op)
      (chartModuleSliceCompSect B S hS X f g T A x)).symm
    F
end Comp

/-! ### The chart-level bridge -/

/-- The transport that the chartwise composition comparison of the pullbacks of modules carries
is the identity: the morphism of algebraic spaces represented by a composite of chart morphisms
is definitionally the composite of the represented morphisms. -/
theorem eqToHom_modulePullback_chartMap_congr {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    eqToHom (congrArg (fun k ↦ modulePullback B S hS k) (chartMap_comp B S hS X f g)) = 𝟙 _ :=
  eqToHom_refl _ _

/-- The chartwise composition comparison of the pullbacks of modules is the composition
comparison of Stacks 03LU for the represented morphisms of the charts, with no transport. -/
theorem chartModuleInverseImageCompApp_eq_modulePullbackCompIso
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V)
    (M : Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2) :
    chartModuleInverseImageCompApp B S hS X f g M =
      (modulePullbackCompIso B S hS (chartMap B S hS X g)
        (chartMap B S hS X f)).hom.app M :=
  (Stacks.CategoryTheory.proj_congr (eqToHom_modulePullback_chartMap_congr B S hS X f g)
      (fun z ↦ (modulePullbackCompIso B S hS (chartMap B S hS X g)
        (chartMap B S hS X f)).hom.app M ≫ NatTrans.app z M)).trans
    (Category.comp_id _)

/-- The comparison of Stacks 03LW at the composite of the represented morphisms of two chart
morphisms is the comparison at the represented morphism of the composite: the two morphisms of
algebraic spaces are definitionally equal. -/
theorem modulePullbackIsoEtaleModulePullback_chartMap_comp {W V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) (g : W ⟶ V) :
    (modulePullbackIsoEtaleModulePullback B S hS
        (chartMap B S hS X g ≫ chartMap B S hS X f)
        (isEtale_chartMap_comp B S hS X f g)).hom =
      (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X (g ≫ f))
        (isEtale_chartMap B S hS X (g ≫ f))).hom :=
  rfl

/-- **The bridge of Stacks 03LU against Stacks 03LW at the étale scheme charts.**  For two
composable morphisms of charts, the two comparisons of Stacks 03LW identifying the chartwise
pullbacks of modules with étale restriction, composed horizontally, equal the chartwise
composition comparison `AlgebraicGeometry.Space.chartModuleInverseImageCompApp` followed by the
comparison of Stacks 03LW for the composite morphism of charts and the strict composition of the
étale restrictions.

The hypothesis is the coefficient-free
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction`, whose own hypothesis
is the equality of the two units of étale restriction along a composite; the three
representability hypotheses it asks for are supplied by
`AlgebraicGeometry.Space.relativelyRepresentable_chartMap`. -/
theorem chartModuleSliceBridge
    (hcoh : ∀ {A' C' D' : AlgebraicSpaces B S hS} (h' : D' ⟶ A') (g' : A' ⟶ C')
      (hh' : IsEtale B S hS h'.hom) (hg' : IsEtale B S hS g'.hom)
      (hhg' : IsEtale B S hS (h' ≫ g').hom),
      yoneda.relativelyRepresentable h'.hom → yoneda.relativelyRepresentable g'.hom →
      yoneda.relativelyRepresentable (h' ≫ g').hom →
      (modulePullbackCompIso B S hS h' g').hom ≫
          (modulePullbackIsoEtaleModulePullback B S hS (h' ≫ g') hhg').hom =
        Functor.whiskerLeft (modulePullback B S hS g')
            (modulePullbackIsoEtaleModulePullback B S hS h' hh').hom ≫
          Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS g' hg').hom
              (etaleModulePullback.{u, u} B S hS h' hh') ≫
            (etaleModulePullbackComp B S hS h' g' hh' hg' hhg').hom)
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V)
    (M : Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2) :
    (chartModuleInverseImage B S hS X g).map
          ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
            (isEtale_chartMap B S hS X f)).hom.app M) ≫
        (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X g)
            (isEtale_chartMap B S hS X g)).hom.app
          ((etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
            (isEtale_chartMap B S hS X f)).obj M) =
      chartModuleInverseImageCompApp B S hS X f g M ≫
        (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X (g ≫ f))
            (isEtale_chartMap B S hS X (g ≫ f))).hom.app M ≫
          etaleModulePullbackCompInvApp B S hS (chartMap B S hS X g) (chartMap B S hS X f)
            (isEtale_chartMap B S hS X g) (isEtale_chartMap B S hS X f)
            (isEtale_chartMap_comp B S hS X f g) M := by
  have hrepc : yoneda.relativelyRepresentable
      (chartMap B S hS X g ≫ chartMap B S hS X f).hom := by
    rw [chartMap_comp]
    exact relativelyRepresentable_chartMap B S hS X (g ≫ f)
  have key := hcoh (chartMap B S hS X g) (chartMap B S hS X f)
    (isEtale_chartMap B S hS X g) (isEtale_chartMap B S hS X f)
    (isEtale_chartMap_comp B S hS X f g) (relativelyRepresentable_chartMap B S hS X g)
    (relativelyRepresentable_chartMap B S hS X f) hrepc
  have keyA := (Stacks.CategoryTheory.proj_congr key (fun z ↦ NatTrans.app z M)).symm
  have keyM := keyA.trans (Stacks.CategoryTheory.proj_congr
    (modulePullbackIsoEtaleModulePullback_chartMap_comp B S hS X f g)
    (fun z ↦ (modulePullbackCompIso B S hS (chartMap B S hS X g)
      (chartMap B S hS X f)).hom.app M ≫ NatTrans.app z M))
  refine ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X g)
    (isEtale_chartMap B S hS X g)).hom.naturality
      ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).hom.app M)).trans ?_
  refine Eq.trans ?_ (Stacks.CategoryTheory.proj_congr
    (chartModuleInverseImageCompApp_eq_modulePullbackCompIso B S hS X f g M).symm
    (fun z ↦ z ≫ (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X (g ≫ f))
        (isEtale_chartMap B S hS X (g ≫ f))).hom.app M ≫
      etaleModulePullbackCompInvApp B S hS (chartMap B S hS X g) (chartMap B S hS X f)
        (isEtale_chartMap B S hS X g) (isEtale_chartMap B S hS X f)
        (isEtale_chartMap_comp B S hS X f g) M))
  exact comp_bridge_uncancel
    ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X g)
        (isEtale_chartMap B S hS X g)).hom.app
      ((modulePullback B S hS (chartMap B S hS X f)).obj M))
    ((etaleModulePullback.{u, u} B S hS (chartMap B S hS X g)
          (isEtale_chartMap B S hS X g)).map
      ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).hom.app M))
    (etaleModulePullbackCompApp B S hS (chartMap B S hS X g) (chartMap B S hS X f)
      (isEtale_chartMap B S hS X g) (isEtale_chartMap B S hS X f)
      (isEtale_chartMap_comp B S hS X f g) M)
    (etaleModulePullbackCompInvApp B S hS (chartMap B S hS X g) (chartMap B S hS X f)
      (isEtale_chartMap B S hS X g) (isEtale_chartMap B S hS X f)
      (isEtale_chartMap_comp B S hS X f g) M)
    ((modulePullbackCompIso B S hS (chartMap B S hS X g)
      (chartMap B S hS X f)).hom.app M)
    ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X (g ≫ f))
      (isEtale_chartMap B S hS X (g ≫ f))).hom.app M)
    (etaleModulePullbackCompApp_comp_inv B S hS (chartMap B S hS X g) (chartMap B S hS X f)
      (isEtale_chartMap B S hS X g) (isEtale_chartMap B S hS X f)
      (isEtale_chartMap_comp B S hS X f g) M) keyM

/-! ### The dictionary square -/

/-- **The first dictionary square of Stacks 03LY, with each dictionary component split into its
two halves.**  This is the form `CategoryTheory.comp_bridge_rearrange_split` consumes. -/
theorem chartModuleInverseImageSliceIso_comp_aux
    (hcoh : ∀ {A' C' D' : AlgebraicSpaces B S hS} (h' : D' ⟶ A') (g' : A' ⟶ C')
      (hh' : IsEtale B S hS h'.hom) (hg' : IsEtale B S hS g'.hom)
      (hhg' : IsEtale B S hS (h' ≫ g').hom),
      yoneda.relativelyRepresentable h'.hom → yoneda.relativelyRepresentable g'.hom →
      yoneda.relativelyRepresentable (h' ≫ g').hom →
      (modulePullbackCompIso B S hS h' g').hom ≫
          (modulePullbackIsoEtaleModulePullback B S hS (h' ≫ g') hhg').hom =
        Functor.whiskerLeft (modulePullback B S hS g')
            (modulePullbackIsoEtaleModulePullback B S hS h' hh').hom ≫
          Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS g' hg').hom
              (etaleModulePullback.{u, u} B S hS h' hh') ≫
            (etaleModulePullbackComp B S hS h' g' hh' hg' hhg').hom)
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V)
    (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    ((chartModuleInverseImage B S hS X g).map
            ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
              (isEtale_chartMap B S hS X f)).hom.app
                ((chartModuleSliceReindex B S hS X U).obj T)) ≫
          (chartModuleInverseImage B S hS X g).map
            (chartModuleSliceTailApp B S hS X f T)) ≫
        (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X g)
              (isEtale_chartMap B S hS X g)).hom.app
            ((chartModuleSliceReindex B S hS X V).obj
              ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T)) ≫
          chartModuleSliceTailApp B S hS X g
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) =
      chartModuleInverseImageCompApp B S hS X f g
          ((chartModuleSliceReindex B S hS X U).obj T) ≫
        ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X (g ≫ f))
                (isEtale_chartMap B S hS X (g ≫ f))).hom.app
              ((chartModuleSliceReindex B S hS X U).obj T) ≫
            chartModuleSliceTailApp B S hS X (g ≫ f) T) ≫
          (chartModuleSliceReindex B S hS X W).map (overMapCompInvApp B S hS X f g T) := by
  have hnat := (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X g)
    (isEtale_chartMap B S hS X g)).hom.naturality (chartModuleSliceTailApp B S hS X f T)
  have hbr := chartModuleSliceBridge B S hS X hcoh f g
    ((chartModuleSliceReindex B S hS X U).obj T)
  have hcps := chartModuleSliceTail_comp B S hS X f g T
  exact comp_bridge_rearrange_split hnat hbr hcps
    (etaleModulePullbackCompInvApp_comp_hom B S hS (chartMap B S hS X g)
      (chartMap B S hS X f) (isEtale_chartMap B S hS X g) (isEtale_chartMap B S hS X f)
      (isEtale_chartMap_comp B S hS X f g) ((chartModuleSliceReindex B S hS X U).obj T))

/-- **The first dictionary square of Stacks 03LY.**  The two readings of the chartwise pullback
of `𝒪`-modules — along the represented morphisms of the charts and along the slices of the small
étale site of `X` — are carried into one another by the dictionary
`AlgebraicGeometry.Space.chartModuleInverseImageSliceApp` compatibly with the composition
comparisons `AlgebraicGeometry.Space.chartModuleInverseImageCompApp` and
`AlgebraicGeometry.Space.overMapCompInvApp`.  This is the identity stated by
`AlgebraicGeometry.Space.ChartModuleInverseImageSliceSquare`, written out as a `∀` so that a
consumer can take it in a binder.

It is the chart-level bridge of Stacks 03LU against Stacks 03LW
(`AlgebraicGeometry.Space.chartModuleSliceBridge`) composed with the coherence of the
restriction-along-equal-functors half (`AlgebraicGeometry.Space.chartModuleSliceTail_comp`), the
two being joined by the naturality of the comparison of Stacks 03LW. -/
theorem chartModuleInverseImageSliceApp_comp
    (hcoh : ∀ {A' C' D' : AlgebraicSpaces B S hS} (h' : D' ⟶ A') (g' : A' ⟶ C')
      (hh' : IsEtale B S hS h'.hom) (hg' : IsEtale B S hS g'.hom)
      (hhg' : IsEtale B S hS (h' ≫ g').hom),
      yoneda.relativelyRepresentable h'.hom → yoneda.relativelyRepresentable g'.hom →
      yoneda.relativelyRepresentable (h' ≫ g').hom →
      (modulePullbackCompIso B S hS h' g').hom ≫
          (modulePullbackIsoEtaleModulePullback B S hS (h' ≫ g') hhg').hom =
        Functor.whiskerLeft (modulePullback B S hS g')
            (modulePullbackIsoEtaleModulePullback B S hS h' hh').hom ≫
          Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS g' hg').hom
              (etaleModulePullback.{u, u} B S hS h' hh') ≫
            (etaleModulePullbackComp B S hS h' g' hh' hg' hhg').hom)
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V)
    (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    (chartModuleInverseImage B S hS X g).map
          (chartModuleInverseImageSliceApp B S hS X f T) ≫
        chartModuleInverseImageSliceApp B S hS X g
          ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) =
      chartModuleInverseImageCompApp B S hS X f g
          ((chartModuleSliceReindex B S hS X U).obj T) ≫
        chartModuleInverseImageSliceApp B S hS X (g ≫ f) T ≫
          (chartModuleSliceReindex B S hS X W).map (overMapCompInvApp B S hS X f g T) := by
  refine Eq.trans (Stacks.CategoryTheory.proj_congr
    (chartModuleInverseImageSliceApp_eq B S hS X f T)
    (fun z ↦ (chartModuleInverseImage B S hS X g).map z ≫
      chartModuleInverseImageSliceApp B S hS X g
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T))) ?_
  refine Eq.trans (Stacks.CategoryTheory.proj_congr
    ((chartModuleInverseImage B S hS X g).map_comp
      ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).hom.app ((chartModuleSliceReindex B S hS X U).obj T))
      (chartModuleSliceTailApp B S hS X f T))
    (fun z ↦ z ≫ chartModuleInverseImageSliceApp B S hS X g
      ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T))) ?_
  refine Eq.trans (Stacks.CategoryTheory.proj_congr
    (chartModuleInverseImageSliceApp_eq B S hS X g
      ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T))
    (fun z ↦ ((chartModuleInverseImage B S hS X g).map
          ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
            (isEtale_chartMap B S hS X f)).hom.app
              ((chartModuleSliceReindex B S hS X U).obj T)) ≫
        (chartModuleInverseImage B S hS X g).map
          (chartModuleSliceTailApp B S hS X f T)) ≫ z)) ?_
  refine Eq.trans ?_ (Stacks.CategoryTheory.proj_congr
    (chartModuleInverseImageSliceApp_eq B S hS X (g ≫ f) T)
    (fun z ↦ chartModuleInverseImageCompApp B S hS X f g
          ((chartModuleSliceReindex B S hS X U).obj T) ≫ z ≫
        (chartModuleSliceReindex B S hS X W).map (overMapCompInvApp B S hS X f g T))).symm
  exact chartModuleInverseImageSliceIso_comp_aux B S hS X hcoh f g T

/-! ### The cocycle condition of Stacks 03LY -/

/-- **The cocycle condition of Stacks 03LY for the chartwise reading of a slice-indexed glueing
datum for modules**, granted the coherence of Stacks 03LU against Stacks 03LW.  The first
dictionary square is `AlgebraicGeometry.Space.chartModuleInverseImageSliceApp_comp`, handed as a
`∀` to
`AlgebraicGeometry.Space.isChartModuleCocycle_sliceToChartModuleTransitionFamily_of_square`.

This is what the chartwise reading of a slice-indexed datum owed: with it the datum of
Stacks 03LY can be assembled from `AlgebraicGeometry.Space.sliceToChartModuleFamily` and
`AlgebraicGeometry.Space.sliceToChartModuleTransitionFamily`. -/
theorem isChartModuleCocycle_sliceToChartModuleTransitionFamily_of_etaleRestriction
    (hcoh : ∀ {A' C' D' : AlgebraicSpaces B S hS} (h' : D' ⟶ A') (g' : A' ⟶ C')
      (hh' : IsEtale B S hS h'.hom) (hg' : IsEtale B S hS g'.hom)
      (hhg' : IsEtale B S hS (h' ≫ g').hom),
      yoneda.relativelyRepresentable h'.hom → yoneda.relativelyRepresentable g'.hom →
      yoneda.relativelyRepresentable (h' ≫ g').hom →
      (modulePullbackCompIso B S hS h' g').hom ≫
          (modulePullbackIsoEtaleModulePullback B S hS (h' ≫ g') hhg').hom =
        Functor.whiskerLeft (modulePullback B S hS g')
            (modulePullbackIsoEtaleModulePullback B S hS h' hh').hom ≫
          Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS g' hg').hom
              (etaleModulePullback.{u, u} B S hS h' hh') ≫
            (etaleModulePullbackComp B S hS h' g' hh' hg' hhg').hom)
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X)) :
    IsChartModuleCocycle B S hS X (sliceToChartModuleFamily B S hS X D)
      (sliceToChartModuleTransitionFamily B S hS X D) :=
  isChartModuleCocycle_sliceToChartModuleTransitionFamily_of_square B S hS X D
    (fun f g T ↦ chartModuleInverseImageSliceApp_comp B S hS X hcoh f g T)

end AlgebraicGeometry.Space

end
