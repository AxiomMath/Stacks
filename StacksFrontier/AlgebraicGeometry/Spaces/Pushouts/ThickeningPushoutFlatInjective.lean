module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutGlueModule
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover

/-!
# A module flat over a pushout embeds into its two restrictions

A quasi-coherent `𝒪_P`-module `M` flat over the pushout `Y'` embeds into its two restrictions:
a morphism `N ⟶ M` killed by `a^*` and by `b^*` is zero.  On an affine chart diagram `W ⟶ T` the
sections `M(W)` are flat over `Γ(T)`, and a flat module over the fibre product
`Γ(T) = Γ(T_Y) ×_{Γ(T_Z)} Γ(T_{Z'})` embeds into its two base changes; the affine chart diagrams
cover `P`.  This is the injectivity in the proof of Stacks 08IW.

## Main results

* `AlgebraicGeometry.Space.ThickeningPushoutSpaces.eq_zero_of_modulePullback_map_eq_zero`.

## References

* [Stacks Project, Tag 08IW](https://stacks.math.columbia.edu/tag/08IW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- The ambient-universe abelian structure on sheaves of modules would be selected ahead of
-- `SheafOfModules.instAbelian` for the `𝒪`-modules here, whose sections live in the universe of
-- the schemes.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

/-- Two sections of a sheaf of modules which agree after restriction along every arrow of a
covering sieve are equal. -/
theorem Stacks.SheafOfModules.section_eq_of_mem {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
    (M : _root_.SheafOfModules.{u} R) {X : C} {T : Sieve X} (hT : T ∈ J X) (x y : M.val.obj (op X))
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X), T f → M.val.map f.op x = M.val.map f.op y) : x = y := by
  have hs := ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
    ((_root_.SheafOfModules.toSheaf R).obj M)).2
  rw [isSheaf_iff_isSheaf_of_type] at hs
  exact (hs T hT).isSeparatedFor.ext fun _ f hf => h f hf

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The chart section along `f` of a section killed by the unit of `f^* ⊣ f_*` is zero. -/
theorem modulePullbackChartSection_eq_zero {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (m : M.val.obj (op d.V))
    (hm : ((modulePullbackAdjunction B S hS f).unit.app M).val.app (op d.V) m = 0) :
    modulePullbackChartSection B S hS f M d m = 0 :=
  (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS f M d m).symm.trans
    ((congrArg (modulePushforwardCounitApp B S hS f ((modulePullback B S hS f).obj M) d) hm).trans
      (map_zero (modulePushforwardCounitAppₛₗ B S hS f ((modulePullback B S hS f).obj M) d)))

namespace ThickeningPushoutSpaces

variable {Z Z' Y Y' : BigFppfOver B S hS} {i : Z ⟶ Z'} {f : Z ⟶ Y} {g : Z' ⟶ Y'} {h : Y ⟶ Y'}
  {P V U' U : AlgebraicSpaces B S hS} {p : P ⟶ (schemeSpaceFunctor B S hS).obj Y'}
  {pV : V ⟶ (schemeSpaceFunctor B S hS).obj Y} {pU' : U' ⟶ (schemeSpaceFunctor B S hS).obj Z'}
  {pU : U ⟶ (schemeSpaceFunctor B S hS).obj Z} {a : V ⟶ P} {b : U' ⟶ P} {c : U ⟶ V} {d : U ⟶ U'}

variable (E : ThickeningPushoutSpaces i f g h p pV pU' pU a b c d)
include E

variable (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom)

/-- **A module flat over `Y'` embeds into its two restrictions, on an affine chart diagram**
(Stacks 08KM, the injectivity in the proof of Stacks 08IW): a section over the chart `W` of a
quasi-coherent module flat over `Y'` whose chart sections on `W_Y` and on `W_{Z'}` vanish is
zero. -/
theorem eq_zero_of_chartSection_eq_zero {M : Modules.{u, u} B S hS P.1 P.2}
    (hM : M.IsQuasicoherentOnSite) (hflat : IsFlatOver B S hS P.2 p.hom M)
    (hU : IsAffine ((SmallEtale.toOver B S hS P.1 ⋙ BigFppfOver.toScheme B S hS).obj dT.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS ((schemeSpaceFunctor B S hS).obj Y').1 ⋙
      BigFppfOver.toScheme B S hS).obj dT.V))
    (m : M.val.obj (op dT.U)) (ha : modulePullbackChartSection B S hS a M (E.dWY dT) m = 0)
    (hb : modulePullbackChartSection B S hS b M (E.dWZ' dT) m = 0) : m = 0 :=
  (E.isRelativeSquare dT hU hV).eq_zero_of_flat
    (flat_sections_of_isFlatOver_chartDiagram B S hS p M hM hflat dT hU hV)
    (isBaseChangeAlong_modulePullbackChartSectionₛₗ B S hS a M hM (E.dWY dT)
      (E.isAffine_WY dT hU) hU)
    (isBaseChangeAlong_modulePullbackChartSectionₛₗ B S hS b M hM (E.dWZ' dT)
      (E.isAffine_WZ' dT hU) hU) m ha hb

/-- **A module flat over `Y'` embeds into its two restrictions** (the injectivity in the proof of
Stacks 08IW): a morphism into a quasi-coherent `𝒪_P`-module flat over `Y'` killed by both units
`M ⟶ a_*a^*M` and `M ⟶ b_*b^*M` is zero. -/
theorem eq_zero_of_comp_unit_eq_zero {M N : Modules.{u, u} B S hS P.1 P.2}
    (hM : M.IsQuasicoherentOnSite) (hflat : IsFlatOver B S hS P.2 p.hom M) (s : N ⟶ M)
    (ha : s ≫ (modulePullbackAdjunction B S hS a).unit.app M = 0)
    (hb : s ≫ (modulePullbackAdjunction B S hS b).unit.app M = 0) : s = 0 := by
  have hchart : ∀ (W : SmallEtale B S hS P.1), HasAffineChartDiagram B S hS p W →
      ∀ n : N.val.obj (op W), s.val.app (op W) n = 0 := by
    rintro W ⟨hW, V, q, hq, hVaff⟩ n
    let dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom :=
      ⟨W, V, q, hq.symm⟩
    refine E.eq_zero_of_chartSection_eq_zero dT hM hflat hW hVaff _ ?_ ?_
    · exact modulePullbackChartSection_eq_zero a M (E.dWY dT) _ <|
        (comp_val_app_op _ _ W n).symm.trans (congrArg (fun k : N ⟶ _ => k.val.app (op W) n) ha)
    · exact modulePullbackChartSection_eq_zero b M (E.dWZ' dT) _ <|
        (comp_val_app_op _ _ W n).symm.trans (congrArg (fun k : N ⟶ _ => k.val.app (op W) n) hb)
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  ext n
  let x := s.val.app U n
  let R : Sieve U.unop := Presheaf.equalizerSieve (F := M.val.presheaf) (X := U) x 0
  have hR : R ∈ SmallEtale.topology B S hS P.1 U.unop :=
    mem_topology_of_hasAffineChartDiagram B S hS p U.unop R fun W a hW => by
      change M.val.map a.op (s.val.app U n) = M.val.map a.op 0
      rw [map_zero]
      exact (PresheafOfModules.naturality_apply s.val (a.op : U ⟶ op W) n).symm.trans
        (hchart W hW _)
  exact Stacks.SheafOfModules.section_eq_of_mem M hR x 0 fun _ f hf => hf

/-- **A module flat over `Y'` embeds into its two restrictions**, in the form of the two inverse
images: a morphism into a quasi-coherent `𝒪_P`-module flat over `Y'` whose inverse images along
`a : V ⟶ P` and along `b : U' ⟶ P` vanish is zero. -/
theorem eq_zero_of_modulePullback_map_eq_zero {M N : Modules.{u, u} B S hS P.1 P.2}
    (hM : M.IsQuasicoherentOnSite) (hflat : IsFlatOver B S hS P.2 p.hom M) (s : N ⟶ M)
    (ha : (modulePullback B S hS a).map s = 0) (hb : (modulePullback B S hS b).map s = 0) :
    s = 0 := by
  refine E.eq_zero_of_comp_unit_eq_zero hM hflat s ?_ ?_ <;>
  · have := (modulePullbackAdjunction B S hS ‹_›).isRightAdjoint
    simp [← Adjunction.unit_naturality, *]

end ThickeningPushoutSpaces

end AlgebraicGeometry.Space

end
