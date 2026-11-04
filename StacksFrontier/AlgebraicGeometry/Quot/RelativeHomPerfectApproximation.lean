module

public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedRelHomDegreeZero
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSpaceStages
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackBoundedAbove
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSingleNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback

/-!
# The perfect approximation of the source module in the proof of Stacks 08JY

The proof of Stacks 08JY starts by choosing, on the Noetherian algebraic space `X`, a perfect
object `P` of `D(𝒪_X)` with a map `α : P ⟶ 𝓕[0]` inducing isomorphisms on `Hⁱ` for `i ≥ 0` and
a surjection on `H⁻¹` (approximation with `m = -1`, Stacks 08HP).  Then `P` has no cohomology in
positive degrees, and for every morphism `h : X' ⟶ X` of algebraic spaces the same holds for
`Lh^*P`, and `α` induces an isomorphism `H⁰(Lh^*P) ≅ h^*𝓕`: `Lh^*` carries `α` to a map which is
still an isomorphism on `H⁰`, and `H⁰(Lh^*(𝓕[0])) ⟶ h^*𝓕` is an isomorphism because `h^*` is right
exact and `Lh^*` is computed on a bounded above flat resolution.  These are exactly the hypotheses
of `CategoryTheory.PullbackData.relHomDegreeZero` for the pullback datum
`AlgebraicGeometry.Space.toposPullbackData`.

On the stages of the proof of Stacks 08K6
(`AlgebraicGeometry.Space.HomSituation.AffineFiniteTypeStageRepresentability`) the space `X` is
Noetherian: it is of finite presentation over an affine scheme of finite type over `ℤ` (Stacks
04ZL).

## Main results

* `AlgebraicGeometry.Space.isIso_homology_singleComparison_toposPullbackData`:
  `H⁰(Lh^*(𝓝[0])) ⟶ h^*𝓝` is an isomorphism.
* `AlgebraicGeometry.Space.isIso_homologyHomFun_singleComparison_of_approximation`: the
  comparison `H⁰(Lh^*P) ⟶ h^*𝓕` induced by an approximation `α` is an isomorphism.
* `AlgebraicGeometry.Space.isLE_smallEtaleDerivedModulePullback_leg_of_approximation` and
  `AlgebraicGeometry.Space.isIso_degreeZeroCompare_toposPullbackData_of_approximation`: the
  hypotheses `hZ` and `hθ` of `CategoryTheory.PullbackData.relHomDegreeZero`.
* `AlgebraicGeometry.Space.bijective_relHomDegreeZero_app_iff_of_approximation`: the degree-zero
  part of the bijectivity at a test object.
* `AlgebraicGeometry.Space.exists_perfect_approximation_degreeZero_of_isNoetherian`: the
  approximation, with these properties, on a Noetherian algebraic space.
* `AlgebraicGeometry.Space.HomSituation.exists_perfect_approximation_degreeZero_of_stage`: the
  same for the source module of a stage of the proof of Stacks 08K6.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
* [Stacks Project, Tag 08HP](https://stacks.math.columbia.edu/tag/08HP)
* [Stacks Project, Tag 04ZL](https://stacks.math.columbia.edu/tag/04ZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

/-- **An approximation of an object in degree zero has no cohomology in positive degrees**: if
`α : E ⟶ F[0]` induces isomorphisms on `Hⁱ` for `i > m` with `m < 0`, then `E` is concentrated in
degrees `≤ 0`. -/
theorem DerivedCategory.isLE_zero_of_isIso_homologyFunctor_map_singleFunctor {C : Type*}
    [Category* C] [Abelian C] [HasDerivedCategory C] {E : DerivedCategory C} {F : C}
    (α : E ⟶ (DerivedCategory.singleFunctor C 0).obj F) (m : ℤ) (hm : m < 0)
    (hiso : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor C i).map α)) :
    E.IsLE 0 :=
  (DerivedCategory.isLE_iff E 0).2 fun i hi => by
    have := hiso i (by omega)
    exact ((DerivedCategory.isLE_iff _ 0).1 inferInstance i hi).of_iso
      (asIso ((DerivedCategory.homologyFunctor C i).map α))

namespace AlgebraicGeometry.Space

/- The derived pullbacks of algebraic spaces are stated on the standard model of the derived
category, so the statements about them here must be too. -/
attribute [local instance] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`H⁰(Lh^*(𝓝[0])) ⟶ h^*𝓝` is an isomorphism**: `𝓝[0]` is resolved by a complex of flat
modules strictly bounded above by `0`, on which the comparison of Stacks 06YY is invertible, and
`h^*` is right exact (Stacks 03DC). -/
theorem isIso_homology_singleComparison_toposPullbackData {X X' : AlgebraicSpaces B S hS}
    (h : X' ⟶ X) (N : toposModules B S hS X) :
    IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS X') 0).map
      ((toposPullbackData B S hS).singleComparison
        (fun f => smallEtaleDerivedModulePullback B S hS f)
        (fun f => smallEtaleDerivedModulePullbackComparison B S hS f) h N)) := by
  classical
  have : ∀ {a b : AlgebraicSpaces B S hS} (f : a ⟶ b),
      PreservesFiniteColimits ((toposPullbackData B S hS).pull f) := fun f =>
    RingedToposHom.pullbackModules_preservesFiniteColimits (smallEtaleRingedToposHom B S hS f)
  let Pflat : ObjectProperty (toposModules B S hS X) := fun F =>
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS X).O) F
  have : Pflat.ContainsZero :=
    ⟨⟨0, isZero_zero _, Stacks.SheafOfModules.KFlatOfSize.isFlat_of_isZero_ofSize _
      (isZero_zero _)⟩⟩
  have hcover : ∀ F : toposModules B S hS X,
      ∃ (G : toposModules B S hS X) (_ : Pflat G) (g : G ⟶ F), Epi g := by
    intro F
    obtain ⟨G, g, hG, hg⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize
      (smallEtaleRingedTopos B S hS X).O F
    exact ⟨G, hG, g, hg⟩
  obtain ⟨G, p, -, hp, hGflat, hGLE⟩ := (CochainComplex.exists_quasiIso_prop Pflat hcover 0).1
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N)
  have := hGLE
  exact PullbackData.isIso_homology_singleComparison_of_resolution _ _ _ h N G hGLE p hp
    (isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat h _
      (isKFlat_of_isStrictlyLE G 0 hGflat))

/-- **The comparison `H⁰(Lh^*P) ⟶ h^*𝓕` induced by an approximation is an isomorphism**: if
`α : P ⟶ 𝓕[0]` induces isomorphisms on `Hⁱ` for `i ≥ 0` and a surjection on `H⁻¹`, so does
`Lh^*α`, and `H⁰(Lh^*(𝓕[0])) ⟶ h^*𝓕` is an isomorphism. -/
theorem isIso_homologyHomFun_singleComparison_of_approximation {X X' : AlgebraicSpaces B S hS}
    (h : X' ⟶ X) {E : toposDerived B S hS X} {F : toposModules B S hS X}
    (α : E ⟶ (DerivedCategory.singleFunctor (toposModules B S hS X) 0).obj F)
    (hiso : ∀ i : ℤ, -1 < i →
      IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS X) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (toposModules B S hS X) (-1)).map α)) :
    IsIso (Stacks.Sites.FibredCategory.homologyHomFun _ _
      ((smallEtaleDerivedModulePullback B S hS h).map α ≫
        (toposPullbackData B S hS).singleComparison
          (fun f => smallEtaleDerivedModulePullback B S hS f)
          (fun f => smallEtaleDerivedModulePullbackComparison B S hS f) h F)) := by
  obtain ⟨h₁, -⟩ := smallEtaleDerivedModulePullback_map_approximation h α (-1) hiso hepi
  have := h₁ 0 (by norm_num)
  have := isIso_homology_singleComparison_toposPullbackData h F
  unfold Stacks.Sites.FibredCategory.homologyHomFun
  rw [Functor.map_comp]
  infer_instance

section DegreeZero

variable {I : Type*} [Category* I] {π : I ⥤ AlgebraicSpaces B S hS} {X : AlgebraicSpaces B S hS}
  (κ : PullbackData.ConeTo π X) {E : toposDerived B S hS X} {F : toposModules B S hS X}
  (α : E ⟶ (DerivedCategory.singleFunctor (toposModules B S hS X) 0).obj F)
  (hiso : ∀ i : ℤ, -1 < i →
    IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS X) i).map α))
  (hepi : Epi ((DerivedCategory.homologyFunctor (toposModules B S hS X) (-1)).map α))

include hiso in
/-- The pullbacks of an approximation `α : P ⟶ 𝓕[0]` along the legs of a cone have no cohomology
in positive degrees: the hypothesis `hZ` of `CategoryTheory.PullbackData.relHomDegreeZero`. -/
theorem isLE_smallEtaleDerivedModulePullback_leg_of_approximation (i : I) :
    ((smallEtaleDerivedModulePullback B S hS (κ.leg i)).obj E).IsLE 0 :=
  have := DerivedCategory.isLE_zero_of_isIso_homologyFunctor_map_singleFunctor α (-1)
    (by norm_num) hiso
  isLE_smallEtaleDerivedModulePullback_obj_of_isLE (κ.leg i) E 0

include hiso hepi in
/-- An approximation `α : P ⟶ 𝓕[0]` induces isomorphisms `H⁰(L(κ i)^*P) ≅ (κ i)^*𝓕`: the
hypothesis `hθ` of `CategoryTheory.PullbackData.relHomDegreeZero`. -/
theorem isIso_degreeZeroCompare_toposPullbackData_of_approximation (i : I) :
    IsIso ((toposPullbackData B S hS).degreeZeroCompare
      (fun f => smallEtaleDerivedModulePullback B S hS f)
      (fun f => smallEtaleDerivedModulePullbackComparison B S hS f) κ E α i) :=
  isIso_homologyHomFun_singleComparison_of_approximation (κ.leg i) α hiso hepi

/-- **The degree-zero part of the bijectivity at a test object**, for an approximation
`α : P ⟶ 𝓕[0]`: the morphism `relHomDegreeZero` of relative Hom functors is bijective at the
test object `i` exactly when composing with the comparison
`smallEtaleDerivedModulePullbackQComparison` of Stacks 08JQ at `𝒢[0]` is. -/
theorem bijective_relHomDegreeZero_app_iff_of_approximation (G : toposModules B S hS X) (i : I) :
    Function.Bijective (((toposPullbackData B S hS).relHomDegreeZero
        (fun f => smallEtaleDerivedModulePullback B S hS f)
        (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
        (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f)
        (hcomp := fun f g => isIso_smallEtaleDerivedComp f g)
        (hid := fun X => isIso_smallEtaleDerivedIdLift X)
        (hZ := fun j => isLE_smallEtaleDerivedModulePullback_leg_of_approximation κ α hiso j)
        (hθ := fun j => isIso_degreeZeroCompare_toposPullbackData_of_approximation κ α hiso hepi j)
        κ E α (toposPullbackData_isCoherent B S hS) G).app (Opposite.op i)) ↔
      Function.Bijective (fun ψ : (smallEtaleDerivedModulePullback B S hS (κ.leg i)).obj E ⟶
          (smallEtaleDerivedModulePullback B S hS (κ.leg i)).obj
            ((DerivedCategory.singleFunctor (toposModules B S hS X) 0).obj G) =>
        ψ ≫ smallEtaleDerivedModulePullbackQComparison (κ.leg i)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)) :=
  have := isLE_smallEtaleDerivedModulePullback_leg_of_approximation κ α hiso
  have := isIso_degreeZeroCompare_toposPullbackData_of_approximation κ α hiso hepi
  bijective_relHomDegreeZero_toposPullbackData_app_iff κ E α G i

end DegreeZero

/-- **The perfect approximation of a module of finite type on a Noetherian algebraic space, in
the form the degree-zero step of Stacks 08JY uses.**  There is a perfect `P` in `D(𝒪_X)` with
`α : P ⟶ 𝓕[0]` inducing isomorphisms on `Hⁱ` for `i ≥ 0` and a surjection on `H⁻¹`; `P` has no
cohomology in positive degrees; and for every morphism `h : X' ⟶ X` of algebraic spaces, `Lh^*P`
has no cohomology in positive degrees and `α` induces an isomorphism `H⁰(Lh^*P) ≅ h^*𝓕`. -/
theorem exists_perfect_approximation_degreeZero_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hXN : IsNoetherian B S hS hZ X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hFt : SheafOfModules.IsFiniteTypeOnSite F) :
    ∃ (E : toposDerived B S hS X)
      (_ : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
      (α : E ⟶ (DerivedCategory.singleFunctor (toposModules B S hS X) 0).obj F),
      (∀ i : ℤ, -1 < i →
        IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS X) i).map α)) ∧
      Epi ((DerivedCategory.homologyFunctor (toposModules B S hS X) (-1)).map α) ∧
      E.IsLE 0 ∧
      ∀ {X' : AlgebraicSpaces B S hS} (h : X' ⟶ X),
        ((smallEtaleDerivedModulePullback B S hS h).obj E).IsLE 0 ∧
        IsIso (Stacks.Sites.FibredCategory.homologyHomFun _ _
          ((smallEtaleDerivedModulePullback B S hS h).map α ≫
            (toposPullbackData B S hS).singleComparison
              (fun f => smallEtaleDerivedModulePullback B S hS f)
              (fun f => smallEtaleDerivedModulePullbackComparison B S hS f) h F)) := by
  obtain ⟨E, hE, α, hiso, hepi⟩ :=
    exists_perfect_approximation_singleFunctor_of_isNoetherian B S hS hZ X hXN F hFt (-1)
  have hLE : E.IsLE 0 :=
    DerivedCategory.isLE_zero_of_isIso_homologyFunctor_map_singleFunctor α (-1) (by norm_num) hiso
  exact ⟨E, hE, α, hiso, hepi, hLE, fun h =>
    ⟨@isLE_smallEtaleDerivedModulePullback_obj_of_isLE _ _ _ _ _ h E 0 hLE,
      isIso_homologyHomFun_singleComparison_of_approximation h α hiso hepi⟩⟩

namespace HomSituation

/-- **The perfect approximation on a stage of the proof of Stacks 08K6.**  Let `v` be a relative
Hom situation over `Spec ℤ` whose base is an affine scheme of finite type over `ℤ`, with `f` of
finite presentation and `𝓕` of finite presentation.  Then `X` is Noetherian, and there is a
perfect `P` in `D(𝒪_X)` with `α : P ⟶ 𝓕[0]` inducing isomorphisms on `Hⁱ` for `i ≥ 0` and a
surjection on `H⁻¹`, such that `P` and every `Lh^*P` have no cohomology in positive degrees and
`α` induces isomorphisms `H⁰(Lh^*P) ≅ h^*𝓕`. -/
theorem exists_perfect_approximation_degreeZero_of_stage
    (T₀ : BigAffineFppf B (⊤_ Scheme.{u}) B.contains_terminal)
    (hT₀ : LocallyOfFiniteType (terminal.from ((BigAffineFppf.toScheme _ _ _).obj T₀)))
    (v : HomSituation B (⊤_ Scheme.{u}) B.contains_terminal)
    (hv : v.base = (schemeSpaceFunctor B (⊤_ Scheme.{u}) B.contains_terminal).obj
      ((BigAffineFppf.inclusion _ _ _).obj T₀))
    (hfp : IsFinitePresentation B (⊤_ Scheme.{u}) B.contains_terminal v.f.hom)
    (hF : v.F.IsFinitePresentationOnSite) :
    IsNoetherian B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal v.X.1 ∧
    ∃ (E : toposDerived B (⊤_ Scheme.{u}) B.contains_terminal v.X)
      (_ : (smallEtaleRingedSite B (⊤_ Scheme.{u}) B.contains_terminal v.X.1 v.X.2).IsPerfect E)
      (α : E ⟶ (DerivedCategory.singleFunctor
        (toposModules B (⊤_ Scheme.{u}) B.contains_terminal v.X) 0).obj v.F),
      (∀ i : ℤ, -1 < i →
        IsIso ((DerivedCategory.homologyFunctor
          (toposModules B (⊤_ Scheme.{u}) B.contains_terminal v.X) i).map α)) ∧
      Epi ((DerivedCategory.homologyFunctor
        (toposModules B (⊤_ Scheme.{u}) B.contains_terminal v.X) (-1)).map α) ∧
      E.IsLE 0 ∧
      ∀ {X' : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal} (h : X' ⟶ v.X),
        ((smallEtaleDerivedModulePullback B (⊤_ Scheme.{u}) B.contains_terminal h).obj E).IsLE 0 ∧
        IsIso (Stacks.Sites.FibredCategory.homologyHomFun _ _
          ((smallEtaleDerivedModulePullback B (⊤_ Scheme.{u}) B.contains_terminal h).map α ≫
            (toposPullbackData B (⊤_ Scheme.{u}) B.contains_terminal).singleComparison
              (fun f => smallEtaleDerivedModulePullback B (⊤_ Scheme.{u}) B.contains_terminal f)
              (fun f => smallEtaleDerivedModulePullbackComparison B (⊤_ Scheme.{u})
                B.contains_terminal f) h v.F)) := by
  have hbase : IsNoetherian B _ _ B.contains_terminal v.base.1 := by
    rw [hv]
    exact isNoetherian_schemeSpace_of_locallyOfFiniteType T₀ hT₀
  have hXN : IsNoetherian B _ _ B.contains_terminal v.X.1 :=
    isNoetherian_of_isFinitePresentation B _ _ B.contains_terminal v.f.hom v.X.2 v.base.2 hfp
      hbase
  have := v.quasicoherent_F
  exact ⟨hXN, exists_perfect_approximation_degreeZero_of_isNoetherian B.contains_terminal v.X hXN
    v.F (SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite v.F)⟩

end HomSituation

end AlgebraicGeometry.Space

end
