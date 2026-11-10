module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartThickeningMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientStructureSheaf
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSurjectiveFlatDualNumbersChart

/-!
# A chart thickening with free ideal is flat over the dual numbers

Let `E` be a square-zero extension `0 → ℐ → 𝒜 → 𝒪_X → 0` on the small étale site of an
algebraic space `X` (the data of Stacks 05ZT) whose ideal is free of rank one, `𝒪_X ≅ ℐ` by
`1 ↦ e`, and let `W'` be the chart thickening of an étale chart `W` of `X`, the scheme with the
space of `W` and structure sheaf `𝒜`. A morphism `α : W' ⟶ S'` to a one-point scheme with
`Γ(S', 𝒪) ≅ k[ε]`, with `ε` pulling back to `e`, is flat, and `W = S ×_{S'} W'` for the closed
point `S ⊆ S'` cut out by `ε`: on an affine open `O` of `W'`, the ring `𝒜(O)` is an extension of
`𝒪_X(O)` by `𝒪_X(O) · e` (`AlgebraicGeometry.flat_and_isPullback_of_dualNumbers_chart`).

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.chartData_of_generator`: the affine chart data.
* `AlgebraicGeometry.Space.SquareZeroExtension.flat_and_isPullback_of_generator`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
  (W : SmallEtale B S hS X.1)
  (s : unitModule B S hS X.2 ⟶ E.I) (t : E.I ⟶ unitModule B S hS X.2)
  (hst : s ≫ t = 𝟙 _) (hts : t ≫ s = 𝟙 _)

/-- The sections `r` of `𝒪_X` go to `r · s(1)`. -/
theorem generator_app (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (r : (smallEtaleRingedTopos B S hS X).O.obj.obj V) :
    ((E.I.val.obj V).smul r).asHom.hom
        (s.val.app V (1 : (structureRingSheaf B S hS X).obj.obj V)) = s.val.app V r := by
  exact (congrArg (fun φ => φ.hom (1 : (structureRingSheaf B S hS X).obj.obj V))
    (ModuleCat.smul_naturality (s.val.app V) r)).trans (congrArg (s.val.app V) (mul_one r))

include hst hts in
/-- **The affine chart data of a chart thickening with free ideal.** -/
theorem chartData_of_generator (O : (E.chartRealizedScheme W).Opens) (hO : IsAffineOpen O)
    (ε : Γ(E.chartRealizedScheme W, O))
    (hε : ε = E.ι (op ((chartOpens B S hS W).obj O))
      (s.val.app (op ((chartOpens B S hS W).obj O))
        (1 : (structureRingSheaf B S hS X).obj.obj (op ((chartOpens B S hS W).obj O))))) :
    Function.Surjective ((E.chartInclusion W).app O).hom ∧
      ∃ incl : Γ(chartScheme W, E.chartInclusion W ⁻¹ᵁ O) →+ Γ(E.chartRealizedScheme W, O),
        Function.Injective incl ∧
        (∀ c, ε * c = incl (((E.chartInclusion W).app O).hom c)) ∧
        (∀ c, ((E.chartInclusion W).app O).hom c = 0 → ∃ d, incl d = c) ∧
        (∀ d, ((E.chartInclusion W).app O).hom (incl d) = 0) ∧
        ∀ d d', incl d * incl d' = 0 := by
  let V : (SmallEtale B S hS X.1)ᵒᵖ := op ((chartOpens B S hS W).obj O)
  let eq := chartΓEquiv W (op O)
  have hA : IsAffineChart B S hS X.1 ((chartOpens B S hS W).obj O) :=
    hO.preimage (E.chartInclusion W)
  have hT : ∀ m, s.val.app V (t.val.app V m) = m := fun m =>
    congrArg (fun φ : E.I ⟶ E.I => φ.val.app V m) hts
  have hS' : ∀ r, t.val.app V (s.val.app V r) = r := fun r =>
    congrArg (fun φ : unitModule B S hS X.2 ⟶ unitModule B S hS X.2 => φ.val.app V r) hst
  let incl : Γ(chartScheme W, E.chartInclusion W ⁻¹ᵁ O) →+ Γ(E.chartRealizedScheme W, O) :=
    (E.ι V).comp ((s.val.app V).hom.toAddMonoidHom.comp eq.symm.toAddMonoidHom)
  refine ⟨fun c' => ?_, incl, ?_, fun c => ?_, fun c hc => ?_, fun d => ?_, fun d d' => ?_⟩
  · obtain ⟨a, ha⟩ := E.surjective_π_app_of_isAffineChart _ hA (eq.symm c')
    exact ⟨a, (congrArg eq ha).trans (eq.apply_symm_apply c')⟩
  · intro d d' h
    have h1 : s.val.app V (eq.symm d) = s.val.app V (eq.symm d') :=
      SquareZeroExtension.injective_ι B S hS E V h
    have h2 := congrArg (t.val.app V) h1
    exact eq.symm.injective ((hS' _).symm.trans (h2.trans (hS' _)))
  · rw [mul_comm ε c, hε]
    exact (E.smul_lift V c _).symm.trans (congrArg (E.ι V) ((E.generator_app s V _).trans
      (congrArg (s.val.app V) (eq.symm_apply_apply _).symm)))
  · obtain ⟨x, hx, -⟩ := E.exact_kernel V c ((E.chartπ_eq_zero_iff W (op O) c).1 hc)
    refine ⟨eq (t.val.app V x), ?_⟩
    refine (congrArg (fun z => E.ι V (s.val.app V z)) (eq.symm_apply_apply _)).trans ?_
    exact (congrArg (E.ι V) (hT x)).trans hx
  · change eq (E.π.hom.app V (E.ι V _)) = 0
    rw [E.mem_kernel]
    exact map_zero _
  · exact E.square_zero V _ _

/-- The section `s(1)` of `ℐ` over a chart, restricted to a smaller chart, is `s(1)`. -/
theorem ι_generator_map {V V' : (SmallEtale B S hS X.1)ᵒᵖ} (m : V ⟶ V') :
    E.A.obj.map m (E.ι V (s.val.app V (1 : (structureRingSheaf B S hS X).obj.obj V))) =
      E.ι V' (s.val.app V' (1 : (structureRingSheaf B S hS X).obj.obj V')) := by
  refine (E.naturality m _).symm.trans (congrArg (E.ι V') ?_)
  refine (PresheafOfModules.naturality_apply s.val m _).symm.trans ?_
  exact congrArg (s.val.app V') (PresheafOfModules.unit_map_one _ m)

include hst hts in
/-- **A chart thickening with free ideal is flat over the dual numbers.** Let `s : 𝒪_X ≅ ℐ` and
let `α : W' ⟶ S'` be a morphism from the chart thickening of an étale chart `W` of `X` to a
one-point scheme with `Γ(S', 𝒪) ≅ k[ε]`, over `f₀ : W ⟶ S₀` and the closed immersion `S₀ ⊆ S'`
cut out by `ε`, with `α^♯ ε = s(1)` on `W' `. Then `α` is flat and `W = S₀ ×_{S'} W'`. -/
theorem flat_and_isPullback_of_generator {k : Type u} [Field k] {S₀ S' : Scheme.{u}}
    (j : S₀ ⟶ S') [AlgebraicGeometry.IsClosedImmersion j] (f₀ : chartScheme W ⟶ S₀)
    (α : E.chartRealizedScheme W ⟶ S') (comm : E.chartInclusion W ≫ α = f₀ ≫ j)
    [Subsingleton S'] (e : TrivSqZeroExt k k ≃+* Γ(S', ⊤))
    (he : ∀ a : TrivSqZeroExt k k, (j.appTop).hom (e a) = 0 ↔ a.fst = 0)
    (hεtop : (α.appTop).hom (e (TrivSqZeroExt.inr 1)) = (E.chartRealizedSchemeΓIso W).hom
      (E.ι (op W) (s.val.app (op W) (1 : (structureRingSheaf B S hS X).obj.obj (op W))))) :
    AlgebraicGeometry.Flat α ∧ IsPullback (E.chartInclusion W) f₀ α j := by
  have : AlgebraicGeometry.IsClosedImmersion (E.chartInclusion W) :=
    (E.isFirstOrderThickening_chartInclusion W).1
  refine flat_and_isPullback_of_dualNumbers_chart (E.chartInclusion W) j f₀ α comm e he
    fun O hO hOV => E.chartData_of_generator W s t hst hts O hO _ ?_
  change (E.chartRealizedScheme W).presheaf.map (homOfLE hOV).op ((α.appTop).hom
    (e (TrivSqZeroExt.inr 1))) = _
  rw [hεtop]
  exact (congrArg ((E.chartRealizedScheme W).presheaf.map (homOfLE hOV).op).hom
    (E.ι_generator_map s (chartOpensTopHom B S hS X W).op)).trans (E.ι_generator_map s _)

end AlgebraicGeometry.Space.SquareZeroExtension

end
