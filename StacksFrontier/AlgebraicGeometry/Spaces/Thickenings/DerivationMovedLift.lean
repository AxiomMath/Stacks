module

public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftDerivationActionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedData
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftComorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftChartKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpRestrictedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftBaseAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftReduction

/-!
# A morphism of first order thickenings over a base, moved by a linear map

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, with inclusion
`i : Z ⟶ X`, let `W₀ ⊆ W` be a closed subspace with inclusion `j : W₀ ⟶ W`, let `q : W ⟶ T` be a
morphism to a base, and let `c : X ⟶ W` be a morphism with `i ≫ c = e₀ ≫ j`.  For an
`𝒪_Z`-linear map `θ : e₀^*Ω_{W₀/T} ⟶ 𝒞_{Z/X}` the proof of [Stacks Project, Tag 04D0] moves the
comorphism of `c` by the `𝒪_T`-derivation `D = d_{W₀/T} ∘ θ` of Equation
[Stacks Project, Tag 0619]:

`g = c^♯ − ι ∘ D ∘ j^♯ : j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`.

This file constructs that pair of solutions of the lifting problem over an arbitrary base `T`,
proves the two facts the gluing of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartLiftSections.lean`
consumes — `g` agrees with `c^♯` on the functions read from the base, and `g` has the same
reduction as `c^♯` — and glues `g` to a unique morphism `b' : X ⟶ W` over `T`.  It is the
base-`T` form of the groupoid construction
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionLiftData`, in which the base is
the space of objects and the structure morphism is the source.

## Main definitions

* `AlgebraicGeometry.Space.movedLiftData`: the pair `(c^♯, g)`, as a
  `Stacks.Sites.LiftDifferenceData` for `j^♯`.

## Main results

* `AlgebraicGeometry.Space.inverseImage_base_comp_movedLiftData_g_eq`: `g` agrees with the
  transported comorphism of `c` after `j^{-1}(q^♯)`.
* `AlgebraicGeometry.Space.movedLiftData_g_comp_reduction_eq`: `g` followed by the reduction
  `i^{-1}𝒪_X ⟶ 𝒪_Z` is `j^♯` followed by the comorphism of `e₀`.
* `AlgebraicGeometry.Space.existsUnique_hom_restrictedSharpThroughThickening_eq_movedLiftData_g`:
  there is exactly one morphism `b' : X ⟶ W` over `T` restricting to `e₀ ≫ j` whose transported
  comorphism is `g` — the existence and uniqueness of [Stacks Project, Tag 04D0] at the level of
  comorphisms, without [Stacks Project, Tag 04KL].

## References

* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (q : W ⟶ T)

variable (hZ : IsFirstOrderThickening B S hS X Z.1) (c : X ⟶ W)
  (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)

/-- **The transported comorphism of `c` and the one it is moved to by the derivation attached
to `θ`**, as a `Stacks.Sites.LiftDifferenceData` for `j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}`.  Its second map
is `g = c^♯ − ι ∘ D ∘ j^♯` with `D = d_{W₀/T} ∘ θ`. -/
noncomputable def movedLiftData
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z) :
    Stacks.Sites.LiftDifferenceData
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀))
      (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ) :=
  liftDifferenceDataOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
    (conormalModule B S hS X Z)
    (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c hc x m)
    θ

/-- The first map of `AlgebraicGeometry.Space.movedLiftData` is the transported comorphism of
`c`. -/
theorem movedLiftData_f
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z) :
    (movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).f =
      restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc := rfl

/-- **The moved solution agrees with the transported comorphism of `c` after `j^{-1}(q^♯)`**:
the two differ by the derivation attached to `θ`, which kills the functions read from `T`. -/
theorem inverseImage_base_comp_movedLiftData_g_eq
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z) :
    (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map (structureSharpRingInverseImage B S hS q) ≫
        (movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).g =
      (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map (structureSharpRingInverseImage B S hS q) ≫
        restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc := by
  have := isLocallySurjective_structureSharpRingInverseImage B S hS
    (subspaceInclusion B S hS W W₀) W₀.2.2
  exact comp_liftDifferenceDataOfHom_g_eq B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
    (conormalModule B S hS X Z)
    (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c hc x m)
    θ
    ((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS W W₀))).map (structureSharpRingInverseImage B S hS q))
    (derivationFamilyOfHom_app_base_eq_zero B S hS Z W₀ e₀ (subspaceInclusion B S hS W W₀ ≫ q) θ
      q (𝟙 T) (Category.comp_id _).symm)

/-- **The moved solution has the same reduction as the transported comorphism of `c`**: its
composite with the direct image along `e₀` of `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` is `j^♯` followed by the
comorphism of `e₀`.  The two solutions differ by a map into the conormal module, which the
reduction kills. -/
theorem movedLiftData_g_comp_reduction_eq
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z) :
    (movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).g ≫
        pullbackRingSheafMap
          (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (smallToposMorphismTypeU B S hS e₀).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀) ≫
        structureSharp B S hS e₀ := by
  have := isLocallySurjective_structureSharpRingInverseImage B S hS
    (subspaceInclusion B S hS W W₀) W₀.2.2
  exact (liftDifferenceDataOfHom_g_comp_eq B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
    (conormalModule B S hS X Z)
    (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c hc x m)
    θ _
    (app_reduction_restrictedSquareZeroValues_ι_eq_zero B S hS Z W₀ e₀ hZ)).trans
    (restrictedSharpThroughThickening_comp_reduction_structureSharp B S hS Z W₀ e₀ c hc)

/-- **The moved solution is the comorphism of a morphism over the base.**  For an `𝒪_Z`-linear
map `θ : e₀^*Ω_{W₀/T} ⟶ 𝒞_{Z/X}` there is a morphism `b' : X ⟶ W` over `T` with the same
restriction `e₀ ≫ j` to the thickening as `c`, whose transported comorphism is the moved
solution `g = c^♯ − ι ∘ D ∘ j^♯`.

The chartwise morphisms which `g` induces over the affine chart diagrams glue, by
`AlgebraicGeometry.Space.exists_hom_eq_thickeningLiftChartSiteHom`, applied with the base `T`
and the structure morphism `q`: its hypothesis on the functions read from `T` is
`AlgebraicGeometry.Space.inverseImage_base_comp_movedLiftData_g_eq`, and the chartwise
morphisms are lifts because `g` has the reduction of `c^♯`
(`AlgebraicGeometry.Space.movedLiftData_g_comp_reduction_eq`).  The glued morphism has `g`
for its comorphism by
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom`
and the injectivity of the transport to the site of `W₀`.  No recovery of morphisms from
morphisms of ringed topoi ([Stacks Project, Tag 04KL]) is used. -/
theorem exists_hom_restrictedSharpThroughThickening_eq_movedLiftData_g
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (p : X ⟶ T) (hcq : c ≫ q = p) :
    ∃ (b' : X ⟶ W) (hb : subspaceInclusion B S hS X Z ≫ b' =
        e₀ ≫ subspaceInclusion B S hS W W₀),
      b' ≫ q = p ∧
        restrictedSharpThroughThickening B S hS Z W₀ b' e₀ hb =
          (movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).g := by
  set g := (movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).g with hg
  have hbase0 := app_liftRestrictedSharpThroughThickening_eq B S hS Z W₀ c e₀ hc q g
    (inverseImage_base_comp_movedLiftData_g_eq B S hS Z W₀ e₀ q hZ c hc θ)
  have hbase := app_thickeningLiftOfIndex_eq_structureSharpThroughThickening B S hS Z c
    (e₀ ≫ subspaceInclusion B S hS W W₀) hc
    (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g) q
    (fun V' s' ↦ hbase0 (op V') s')
  have hred := thickeningLiftOfIndex_comp_reduction B S hS Z c _ hc _
    (liftRestrictedSharpThroughThickening_comp_reduction B S hS Z W₀ e₀ g
      (movedLiftData_g_comp_reduction_eq B S hS Z W₀ e₀ q hZ c hc θ))
  have hres0 : Z.1.ι ≫ c.hom = (e₀ ≫ subspaceInclusion B S hS W W₀).hom :=
    congrArg (fun n : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W ↦ n.hom) hc
  have hcq' : c.hom ≫ q.hom = p.hom := congrArg (fun n : X ⟶ T ↦ n.hom) hcq
  obtain ⟨ε, hsrc, hres, hchart⟩ := exists_hom_eq_thickeningLiftChartSiteHom B S hS Z hZ.1 c
    (thickeningLiftOfIndex B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) hc
      (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g))
    q hbase p q (e₀ ≫ subspaceInclusion B S hS W W₀).hom
    (fun V _ jc ψ hV hψ ↦ by
      obtain ⟨-, V', q', hq, hV'aff⟩ := hV
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS T.1).obj V')) := hV'aff
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS W.1).obj
            (indexOfChartDiagram B S hS q (⟨V, V', q', hq.symm⟩ :
              ChartDiagram B S hS W.1 T.1 q.hom)).right.unop)) :=
        (inferInstance : IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS W.1).obj V)))
      refine ⟨?_, fun Ww k t hkt ↦ ?_⟩
      · refine (yoneda_map_comp_chart_hom_comp_eq_of_index B S hS Z hZ.1 c
          (e₀ ≫ subspaceInclusion B S hS W W₀) hc
          (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g) q V'
          (indexOfChartDiagram B S hS q (⟨V, V', q', hq.symm⟩ :
            ChartDiagram B S hS W.1 T.1 q.hom)) jc
          (fun s ↦ hbase0 _ s) ψ hψ).trans ?_
        rw [hcq']
      · refine (yoneda_map_comp_chart_hom_eq_restriction B S hS Z hZ.1 c _ hred V jc ψ hψ
          Ww k t hkt).trans ?_
        rw [hres0])
  refine ⟨ObjectProperty.homMk ε, ObjectProperty.hom_ext _ hres,
    ObjectProperty.hom_ext _ hsrc, ?_⟩
  have hA : structureSharpThroughThickeningAt B S hS Z (ObjectProperty.homMk ε)
        (e₀ ≫ subspaceInclusion B S hS W W₀) (ObjectProperty.hom_ext _ hres) =
      liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g := by
    refine structureSharpThroughThickeningAt_eq_of_eq_thickeningLiftOfIndex B S hS Z c
      (ObjectProperty.homMk ε) _ hc (ObjectProperty.hom_ext _ hres) _ ?_
    exact structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom B S hS Z hZ.1 c
      (ObjectProperty.homMk ε) _ _ hred q hbase fun Q hQaff jc ψ hψ ↦ @hchart Q hQaff jc ψ hψ
  exact liftRestrictedSharpThroughThickening_injective B S hS Z W₀ e₀ _ _
    ((liftRestrictedSharpThroughThickening_restrictedSharpThroughThickening B S hS Z W₀
      (ObjectProperty.homMk ε) e₀ (ObjectProperty.hom_ext _ hres)).trans hA)

/-- **Existence and uniqueness of the morphism moved by `θ`.**  There is exactly one morphism
`b' : X ⟶ W` over `T`, restricting to `e₀ ≫ j` on the thickening, whose transported comorphism
is the moved solution `g = c^♯ − ι ∘ D ∘ j^♯`, `D = d_{W₀/T} ∘ θ`.  Existence is
`AlgebraicGeometry.Space.exists_hom_restrictedSharpThroughThickening_eq_movedLiftData_g`;
uniqueness is `AlgebraicGeometry.Space.eq_of_restrictedSharpThroughThickening_eq`, two morphisms
agreeing on a first order thickening being determined by their transported comorphisms.  This is
the content of [Stacks Project, Tag 04D0] at the level of comorphisms. -/
theorem existsUnique_hom_restrictedSharpThroughThickening_eq_movedLiftData_g
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (p : X ⟶ T) (hcq : c ≫ q = p) :
    ∃! b' : X ⟶ W, ∃ (hb : subspaceInclusion B S hS X Z ≫ b' =
        e₀ ≫ subspaceInclusion B S hS W W₀),
      b' ≫ q = p ∧
        restrictedSharpThroughThickening B S hS Z W₀ b' e₀ hb =
          (movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).g := by
  obtain ⟨b', hb, hbq, hbg⟩ :=
    exists_hom_restrictedSharpThroughThickening_eq_movedLiftData_g B S hS Z W₀ e₀ q hZ c hc θ
      p hcq
  exact ⟨b', ⟨hb, hbq, hbg⟩, fun b'' ⟨hb'', _, hbg''⟩ ↦
    eq_of_restrictedSharpThroughThickening_eq B S hS Z hZ W₀ b'' b' e₀ hb'' hb
      (hbg''.trans hbg.symm)⟩

/-- The sectionwise difference of `AlgebraicGeometry.Space.movedLiftData` is the derivation
attached to `θ` by Equation [Stacks Project, Tag 0619], read through `j^♯`. -/
theorem movedLiftData_diff
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V)) :
    (movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).diff x =
      derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
        (conormalModule B S hS X Z) θ V
        ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x) := by
  dsimp only [movedLiftData, liftDifferenceDataOfHom, Stacks.Sites.derivationActionData]

/-- **The moved solution on sections**: `c^♯ x − g x = ι(D(j^♯ x))`, with `D = d_{W₀/T} ∘ θ`
the derivation attached to `θ` by Equation [Stacks Project, Tag 0619]. -/
theorem ι_derivationFamilyOfHom_eq_sub_movedLiftData_g
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V)) :
    (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
        (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
          (conormalModule B S hS X Z) θ V
          ((structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).hom.app V x)) =
      (movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).f.hom.app V x -
        (movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).g.hom.app V x := by
  simpa only [movedLiftData_diff] using (movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).ι_diff x

/-- **A morphism is determined by its difference with `c`.**  Two morphisms `b₁, b₂ : X ⟶ W`
restricting to `e₀ ≫ j` whose transported comorphisms differ from that of `c` by the same
`ι ∘ D ∘ j^♯` are equal: their transported comorphisms agree, and a morphism agreeing with
another on a first order thickening is determined by its transported comorphism. -/
theorem eq_of_ι_derivationFamilyOfHom_eq_sub
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (b₁ b₂ : X ⟶ W)
    (hb₁ : subspaceInclusion B S hS X Z ≫ b₁ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hb₂ : subspaceInclusion B S hS X Z ≫ b₂ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h₁ : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
          (x : ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).obj.obj V)),
      (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
              (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
                (conormalModule B S hS X Z) θ V
                ((structureSharpRingInverseImage B S hS
                  (subspaceInclusion B S hS W W₀)).hom.app V x)) =
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
          (restrictedSharpThroughThickening B S hS Z W₀ b₁ e₀ hb₁).hom.app V x)
    (h₂ : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
          (x : ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).obj.obj V)),
      (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
              (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
                (conormalModule B S hS X Z) θ V
                ((structureSharpRingInverseImage B S hS
                  (subspaceInclusion B S hS W W₀)).hom.app V x)) =
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
          (restrictedSharpThroughThickening B S hS Z W₀ b₂ e₀ hb₂).hom.app V x) :
    b₁ = b₂ := by
  refine eq_of_restrictedSharpThroughThickening_eq B S hS Z hZ W₀ b₁ b₂ e₀ hb₁ hb₂ ?_
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦
    RingCat.hom_ext (RingHom.ext fun x ↦ ?_)))
  exact sub_right_injective ((h₁ (V := V) (x := x)).symm.trans (h₂ (V := V) (x := x)))

/-- **The morphism moved by `θ` satisfies the conditions of [Stacks Project, Tag 04D0]**, read
through the moved solution `g`: a morphism whose transported comorphism is `g` agrees with `c`
on the sections killed by `j^♯`, and differs from it by `ι ∘ D ∘ j^♯`. -/
theorem agree_and_ι_derivationFamilyOfHom_of_eq_movedLiftData_g
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (b' : X ⟶ W)
    (hb : subspaceInclusion B S hS X Z ≫ b' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hbg : restrictedSharpThroughThickening B S hS Z W₀ b' e₀ hb =
      (movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).g)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
          (x : ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).obj.obj V)) :
    ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x =
          0 →
        (restrictedSharpThroughThickening B S hS Z W₀ b' e₀ hb).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x) ∧
      (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
              (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
                (conormalModule B S hS X Z) θ V
                ((structureSharpRingInverseImage B S hS
                  (subspaceInclusion B S hS W W₀)).hom.app V x)) =
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
          (restrictedSharpThroughThickening B S hS Z W₀ b' e₀ hb).hom.app V x := by
  have hD := ι_derivationFamilyOfHom_eq_sub_movedLiftData_g B S hS Z W₀ e₀ q hZ c hc θ V x
  have hgx := ringSheafHom_congr_app_apply hbg V x
  refine ⟨fun hx ↦ ?_, hD.trans (congrArg (fun t ↦
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x - t) hgx.symm)⟩
  refine hgx.trans ((movedLiftData B S hS Z W₀ e₀ q hZ c hc θ).app_eq_of_app_eq_zero x hx).symm

/-- **[Stacks Project, Tag 04D0], with condition (2) read on the defining ideal.**  For an
`𝒪_Z`-linear map `θ : e₀^*Ω_{W₀/T} ⟶ 𝒞_{Z/X}` there is exactly one morphism `b' : X ⟶ W` over
`T` with `i ≫ b' = e₀ ≫ j` such that the transported comorphisms of `c` and `b'` agree on the
sections killed by `j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}` and differ by `ι ∘ D ∘ j^♯`, `D = d_{W₀/T} ∘ θ`.

Uniqueness uses only the last condition.  The registered form, with condition (2) stated as the
equality of the two maps of [Stacks Project, Tag 04CP], is derived from this one. -/
theorem existsUnique_hom_agreeOnIdeal_derivation_eq
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (p : X ⟶ T) (hcq : c ≫ q = p) :
    ∃! b' : X ⟶ W, ∃ (hb : subspaceInclusion B S hS X Z ≫ b' =
        e₀ ≫ subspaceInclusion B S hS W W₀),
      b' ≫ q = p ∧
        (∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
          (x : ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).obj.obj V)),
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x =
              0 →
            (restrictedSharpThroughThickening B S hS Z W₀ b' e₀ hb).hom.app V x =
              (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x) ∧
        ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
          (x : ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).obj.obj V)),
          (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
              (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
                (conormalModule B S hS X Z) θ V
                ((structureSharpRingInverseImage B S hS
                  (subspaceInclusion B S hS W W₀)).hom.app V x)) =
            (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
              (restrictedSharpThroughThickening B S hS Z W₀ b' e₀ hb).hom.app V x := by
  obtain ⟨b', hb, hbq, hbg⟩ :=
    exists_hom_restrictedSharpThroughThickening_eq_movedLiftData_g B S hS Z W₀ e₀ q hZ c hc θ
      p hcq
  have h := fun V x ↦ agree_and_ι_derivationFamilyOfHom_of_eq_movedLiftData_g B S hS Z W₀ e₀ q hZ
    c hc θ b' hb hbg V x
  refine ⟨b', ⟨hb, hbq, fun V x ↦ (h V x).1, fun V x ↦ (h V x).2⟩, ?_⟩
  rintro b'' ⟨hb'', -, -, hD''⟩
  exact eq_of_ι_derivationFamilyOfHom_eq_sub B S hS Z W₀ e₀ q hZ c hc θ b'' b' hb'' hb
    (fun {V x} ↦ hD'' V x) (fun {V x} ↦ (h V x).2)

end AlgebraicGeometry.Space

end
