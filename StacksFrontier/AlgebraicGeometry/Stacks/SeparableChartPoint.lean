module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChartPoint
public import StacksFrontier.Deformation.Artin.SliceTangentSpace

/-!
# A smooth chart point with residue field exactly a finite separable extension

In the versal situation of Stacks 0DQU — an algebraic stack `𝒳` locally of finite type over a
locally Noetherian scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a point with `k` of finite type over
`S`. The proof of Stacks 0DSB needs a smooth scheme chart `g : V ⟶ 𝒳` and a point
`ν : Spec l ⟶ V` over `x₀`, for a finite separable extension `l/k`, at which the residue field of
`V` is *exactly* `l`. This file produces it in two steps.

1. **Stacks 07W4 at a chart.** For a smooth surjective chart `g`, the base change of `g` along
  `x₀` is smooth and surjective over `Spec k`; on a smooth surjective scheme `T ⟶ Spec k` along
  which `x₀` lifts (`AlgebraicGeometry.Stack.exists_scheme_lift_of_isSurjective_isSmooth`),
  Stacks 056U gives a closed point with residue field `l` finite separable over `k`
  (`AlgebraicGeometry.Stack.exists_separable_extension_chart_point`).
2. **The `𝔸^n_V` trick.** The residue field `κ(v)` of the image of `Spec l ⟶ V` may be smaller
  than `l`. Choosing generators `α₁, …, αₙ` of `l` as a `Λ`-algebra (for an affine open
  `Spec Λ ⊆ S` with `l` of finite type over `Λ`), the point `(ν, α) : Spec l ⟶ 𝔸^n_V` has
  residue field `l`, and `𝔸^n_V ⟶ V ⟶ 𝒳` is still smooth
  (`AlgebraicGeometry.Stack.exists_affineSpace_chartPoint`). In fact the ring map of *every* affine
  chart of `𝔸^n_V` at the new point onto `l` is surjective, since its image contains `Λ` and the
  coordinates `αᵢ`.

## Main results

* `AlgebraicGeometry.Stack.exists_separable_extension_chart_point`: step 1.
* `AlgebraicGeometry.Stack.exists_affineSpace_chartPoint`: step 2.
* `AlgebraicGeometry.Stack.surjective_residueFieldMap_of_surjective_ringMap`: a surjective chart
  ring map makes the residue field map surjective.
* `AlgebraicGeometry.Stack.exists_smoothChart_point_residueField_eq`: the combination, in the
  form used by the proof of Stacks 0DSB.

## References

* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 07W4](https://stacks.math.columbia.edu/tag/07W4)
* [Stacks Project, Tag 0DSB](https://stacks.math.columbia.edu/tag/0DSB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion

open Deformation.Artin.SliceTangent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}


/-- **A point of a smooth surjective chart over a finite separable extension (Stacks 07W4 at a
chart).** Let `g : (Sch/V) ⟶ 𝒳` be a smooth surjective 1-morphism of algebraic stacks and `x₀` an
object of `𝒳` over `Spec k`. Then for some finite separable extension `l/k` there are an object
`u₀` of `(Sch/V)` over `Spec l` and an arrow `g(u₀) ⟶ x₀` lying over `Spec l ⟶ Spec k`. -/
theorem exists_separable_extension_chart_point
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (V : BigFppfOver B S hS)
    (g : schemeStack.{u, w} B S hS V ⟶ 𝒳) (hsurj : IsSurjective B S hS g)
    (hsm : AlgebraicStacks.IsSmooth B S hS g)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : 𝒳.val.val.obj)
    (hx₀ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ∃ (l : Type u) (_ : Field l) (_ : Algebra k l) (_ : Algebra Λ l) (_ : IsScalarTower Λ k l),
      Module.Finite k l ∧ Algebra.IsSeparable k l ∧
      ∃ (u₀ : Over V)
        (_hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
        (hxₗ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj
            ((CatFiberedInGroupoids.homFunctor g.hom).obj u₀) =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
        (η : (CatFiberedInGroupoids.homFunctor g.hom).obj u₀ ⟶ x₀),
        eqToHom (congrArg Over.left hxₗ).symm ≫
            ((𝒳.val.val.p ⋙ Over.post B.inclusion).map η).left ≫
          eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)) := by
  classical
  let U := 𝒳.val.val.p.obj x₀
  let y : 𝒳.val.val.p.Fiber U := ⟨x₀, rfl⟩
  obtain ⟨T, m, hsmooth, hsurjm, z, φ, hφ⟩ :=
    exists_scheme_lift_of_isSurjective_isSmooth B S hS g hsurj hsm U y
  have hU : B.inclusion.obj U.left = Spec (.of k) := congrArg Over.left hx₀
  let X : Scheme.{u} := B.inclusion.obj T
  let gk : X ⟶ Spec (.of k) := B.inclusion.map m ≫ eqToHom hU
  have : Smooth gk := inferInstance
  have : Surjective gk := inferInstance
  obtain ⟨t₀, -⟩ := gk.surjective (IsLocalRing.closedPoint k)
  have : Nonempty X := ⟨t₀⟩
  obtain ⟨t, -, hfin, hsep⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth gk).nonempty
  let algkl : Algebra k (X.residueField t) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ gk.appTop ≫ X.Γevaluation t).hom.toAlgebra
  let algΛl : Algebra Λ (X.residueField t) :=
    ((algebraMap k (X.residueField t)).comp (algebraMap Λ k)).toAlgebra
  obtain ⟨u₀, hu₀, hxₗ, η, hη⟩ :=
    Deformation.Artin.exists_chart_point_of_lift 𝒳.val V g.hom iΛ x₀ hx₀ T m z φ hφ t
  exact ⟨_, inferInstance, algkl, algΛl, IsScalarTower.of_algebraMap_eq (fun _ => rfl), hfin,
    hsep, u₀, hu₀, hxₗ, η, hη⟩

/-- **The `𝔸^n_V` trick.** Let `g : (Sch/V) ⟶ 𝒳` be smooth and let `u₀` be an object of
`(Sch/V)` over `Spec l ⟶ Spec Λ ⟶ S`, with `l` of finite type over `Λ`. Then there are a smooth
`g' : (Sch/V') ⟶ 𝒳` (with `V' = 𝔸^n_V`) and an object `u₀'` of `(Sch/V')` over the same
`Spec l` with `g'(u₀') = g(u₀)`, such that the ring map onto `l` of every affine chart of `V'` at
the point of `u₀'` is surjective: the residue field of `V'` there is exactly `l`. -/
theorem exists_affineSpace_chartPoint
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (V : BigFppfOver B S hS)
    (g : schemeStack.{u, w} B S hS V ⟶ 𝒳) (hg : AlgebraicStacks.IsSmooth B S hS g)
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l] [Algebra.FiniteType Λ l]
    (iΛ : Spec (.of Λ) ⟶ S) [_root_.AlgebraicGeometry.IsOpenImmersion iΛ]
    (u₀ : Over V)
    (hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ)) :
    ∃ (V' : BigFppfOver B S hS) (g' : schemeStack.{u, w} B S hS V' ⟶ 𝒳) (u₀' : Over V')
      (hu₀' : (Over.forget V' ⋙ Over.post B.inclusion).obj u₀' =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ)),
      AlgebraicStacks.IsSmooth B S hS g' ∧
      (CatFiberedInGroupoids.homFunctor g'.hom).obj u₀' =
        (CatFiberedInGroupoids.homFunctor g.hom).obj u₀ ∧
      ∀ c : AffineChart iΛ (B.inclusion.map V'.hom) ((pointMap hu₀').base (closedPt (.of l))),
        Function.Surjective (c.ringMap (pointMap hu₀') (range_pointMap c)) := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra Λ l).FG)
  let n : Type u := ↥s
  let X : Scheme.{u} := B.inclusion.obj V.left
  have hA : B.Contains (AffineSpace n X) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (AffineSpace n X ↘ X) V.left.2
  let pr : B.obj hA ⟶ V.left := ObjectProperty.homMk (AffineSpace n X ↘ X)
  let V' : BigFppfOver B S hS := Over.mk (pr ≫ V.hom)
  let P : V' ⟶ V := Over.homMk pr rfl
  have hPsm : Smooth ((BigFppfOver.toScheme B S hS).map P) := smooth_affineSpace_over n X
  let g' := schemeStackMap.{u, w} B S hS P ≫ g
  let Y : Scheme.{u} := B.inclusion.obj u₀.left.left
  have hY : Y = Spec (.of l) := congrArg Over.left hu₀
  let v : n → Γ(Y, ⊤) := fun i => (eqToHom hY).appTop
    ((Scheme.ΓSpecIso (.of l)).inv (i : l))
  let mS : Y ⟶ AffineSpace n X := AffineSpace.homOfVector (B.inclusion.map u₀.hom.left) v
  have hmS : mS ≫ (AffineSpace n X ↘ X) = B.inclusion.map u₀.hom.left :=
    AffineSpace.homOfVector_over _ _
  let m : u₀.left ⟶ V' := Over.homMk (ObjectProperty.homMk mS) (by
    apply B.inclusion.map_injective
    change B.inclusion.map (ObjectProperty.homMk mS ≫ pr ≫ V.hom) = B.inclusion.map u₀.left.hom
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc]
    change (mS ≫ (AffineSpace n X ↘ X)) ≫ _ = _
    rw [hmS, ← Functor.map_comp, Over.w u₀.hom])
  let u₀' : Over V' := Over.mk m
  have hu₀' : (Over.forget V' ⋙ Over.post B.inclusion).obj u₀' =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) := hu₀
  refine ⟨V', g', u₀', hu₀', AlgebraicStacks.isSmooth_comp B S hS _ _
    (isSmooth_schemeStackMap.{u, w} B S hS P hPsm) hg, ?_, ?_⟩
  · change (CatFiberedInGroupoids.homFunctor g.hom).obj ((Over.map P).obj u₀') = _
    congr 1
    have hmP : m ≫ P = u₀.hom := by
      ext
      exact hmS
    change Over.mk (m ≫ P) = u₀
    rw [hmP]
    rfl
  · intro c
    have hpt : pointMap hu₀' = eqToHom hY.symm ≫ mS := rfl
    set ψ := c.ringMap (pointMap hu₀') (range_pointMap c) with hψ
    let ρ : CommRingCat.of (MvPolynomial n (ULift.{u} ℤ)) ⟶ c.ring :=
      Spec.preimage (c.fromSpec ≫ AffineSpace.toSpecMvPoly n X)
    have hρ : Spec.map ρ = c.fromSpec ≫ AffineSpace.toSpecMvPoly n X := Spec.map_preimage _
    have hcomp : Spec.map (ρ ≫ ψ) = pointMap hu₀' ≫ AffineSpace.toSpecMvPoly n X := by
      rw [Spec.map_comp, hρ, ← Category.assoc, c.spec_ringMap]
    have hcoord : ∀ i : n, ψ (ρ (MvPolynomial.X i)) = (i : l) := by
      intro i
      have h := congrArg (fun φ => (AffineSpace.toSpecMvPolyIntEquiv n φ) i) hcomp
      simp only [AffineSpace.toSpecMvPolyIntEquiv_apply] at h
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
      change _ = (pointMap hu₀').appTop (AffineSpace.coord X i) at h
      have hpc : (pointMap hu₀').appTop (AffineSpace.coord X i) =
          (Scheme.ΓSpecIso (.of l)).inv (i : l) := by
        rw [hpt, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          eqToHom_trans, eqToHom_refl, Scheme.Hom.id_appTop, CommRingCat.id_apply]
      rw [hpc] at h
      exact (Scheme.ΓSpecIso (.of l)).commRingCatIsoToRingEquiv.symm.injective h
    have hΛ : ∀ a : Λ, ψ (c.structureMap a) = algebraMap Λ l a := by
      intro a
      have h := c.structureMap_ringMap (CommRingCat.ofHom (algebraMap Λ l)) (pointMap hu₀')
        (range_pointMap c) (pointMap_comp (hv₀ := hu₀'))
      rw [← hψ] at h
      have h' := congrArg (fun φ => φ a) h
      simp only [CommRingCat.hom_ofHom] at h'
      exact h'
    intro x
    have hx : x ∈ Algebra.adjoin Λ (s : Set l) := hs ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact ⟨ρ (MvPolynomial.X ⟨x, hx⟩), hcoord ⟨x, hx⟩⟩
    | algebraMap a => exact ⟨c.structureMap a, hΛ a⟩
    | add x y _ _ hx hy => exact add_mem (s := ψ.hom.range) hx hy
    | mul x y _ _ hx hy => exact mul_mem (s := ψ.hom.range) hx hy

/-- If the ring map out of an affine chart attached to a field-valued point `Spec l ⟶ Y` is
surjective, then so is the map `κ(y) ⟶ l` from the residue field at its image point: the chart
map factors through it. -/
theorem surjective_residueFieldMap_of_surjective_ringMap {Y : Scheme.{u}} {s : Y ⟶ S}
    {Λ l : Type u} [CommRing Λ] [Field l] {iΛ : Spec (.of Λ) ⟶ S}
    [_root_.AlgebraicGeometry.IsOpenImmersion iΛ] (pt : Spec (.of l) ⟶ Y)
    (c : AffineChart iΛ s (pt.base (closedPt (.of l)))) (hpt : Set.range pt.base ⊆ c.U)
    (hc : Function.Surjective (c.ringMap pt hpt)) :
    Function.Surjective (Scheme.SpecToEquivOfField l Y pt).2 := by
  set xf := Scheme.SpecToEquivOfField l Y pt with hxf
  have hfac : pt = Spec.map xf.2 ≫ Y.fromSpecResidueField xf.1 :=
    ((Scheme.SpecToEquivOfField l Y).left_inv pt).symm
  have hr : Set.range (Y.fromSpecResidueField xf.1).base ⊆ c.U := by
    rw [Scheme.range_fromSpecResidueField, Set.singleton_subset_iff]
    exact c.mem
  have hr' : Set.range (Spec.map xf.2 ≫ Y.fromSpecResidueField xf.1).base ⊆ c.U := hfac ▸ hpt
  have hcomp : c.ringMap pt hpt = c.ringMap (Y.fromSpecResidueField xf.1) hr ≫ xf.2 := by
    rw [AffineChart.ringMap_congr c hpt hr' hfac, AffineChart.ringMap_comp]
  intro x
  obtain ⟨a, ha⟩ := hc x
  rw [hcomp, CommRingCat.comp_apply] at ha
  exact ⟨_, ha⟩

/-- **A smooth chart point with residue field exactly a finite separable extension (the chart
step of the proof of Stacks 0DSB).** In the versal situation of Stacks 0DQU, let `x₀` be an object
of `𝒳` over `Spec k ⟶ Spec Λ ⟶ S`, for an affine open `Spec Λ ⊆ S` and `k` of finite type over
`Λ`. Then there are a finite separable extension `l/k`, a smooth 1-morphism `g : (Sch/V) ⟶ 𝒳`
from a scheme `V` locally of finite type over `S`, an object `u₀` of `(Sch/V)` over
`Spec l ⟶ Spec Λ ⟶ S` and an arrow `η : g(u₀) ⟶ x₀` over `Spec l ⟶ Spec k`, such that the
residue field of `V` at the point `ν : Spec l ⟶ V` of `u₀` is exactly `l`: the residue field map
`κ(ν) ⟶ l` is surjective, and so is the ring map onto `l` of every affine chart of `V` at `ν`
(there is one). -/
theorem exists_smoothChart_point_residueField_eq (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ∃ (l : Type u) (_ : Field l) (_ : Algebra k l) (_ : Algebra Λ l) (_ : IsScalarTower Λ k l),
      Module.Finite k l ∧ Algebra.IsSeparable k l ∧
      ∃ (V : BigFppfOver D.B D.S D.hS) (g : schemeStack.{u, w} D.B D.S D.hS V ⟶ D.𝒳),
        AlgebraicStacks.IsSmooth D.B D.S D.hS g ∧ LocallyOfFiniteType (D.B.inclusion.map V.hom) ∧
      ∃ (u₀ : Over V)
        (hu₀ : (Over.forget V ⋙ Over.post D.B.inclusion).obj u₀ =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
        (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj
            ((CatFiberedInGroupoids.homFunctor g.hom).obj u₀) =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
        (η : (CatFiberedInGroupoids.homFunctor g.hom).obj u₀ ⟶ x₀),
        eqToHom (congrArg Over.left hxₗ).symm ≫
            ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
          eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)) ∧
        Nonempty (AffineChart iΛ (D.B.inclusion.map V.hom)
          ((pointMap hu₀).base (closedPt (.of l)))) ∧
        (∀ c : AffineChart iΛ (D.B.inclusion.map V.hom) ((pointMap hu₀).base (closedPt (.of l))),
          Function.Surjective (c.ringMap (pointMap hu₀) (range_pointMap c))) ∧
        Function.Surjective (Scheme.SpecToEquivOfField l _ (pointMap hu₀)).2 := by
  let : _root_.AlgebraicGeometry.IsOpenImmersion iΛ := hiΛ
  obtain ⟨V₀, g₀, hg₀sm, hg₀surj⟩ := exists_smooth_surjective_schemeStack.{u, w} D.B D.S D.hS D.𝒳
  obtain ⟨l, _, _, _, _, hkl, hsep, u₀, hu₀, hxₗ, η, hη⟩ :=
    exists_separable_extension_chart_point D.𝒳 V₀ g₀ hg₀surj hg₀sm iΛ x₀ hx₀
  have hΛk : Algebra.FiniteType Λ k := by
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k))) :=
      have := hfinite.1
      locallyOfFiniteType_of_comp _ iΛ
    exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp this)
  have : Algebra.FiniteType k l := inferInstance
  have : Algebra.FiniteType Λ l := Algebra.FiniteType.trans hΛk inferInstance
  obtain ⟨V, g, u₀', hu₀', hgsm, hobj, hsurj⟩ :=
    exists_affineSpace_chartPoint D.𝒳 V₀ g₀ hg₀sm iΛ u₀ hu₀
  have hxₗ' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj
      ((CatFiberedInGroupoids.homFunctor g.hom).obj u₀') =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) := by
    rw [hobj]; exact hxₗ
  have key : ∀ (x' : D.𝒳.val.val.obj) (h : x' = (CatFiberedInGroupoids.homFunctor g₀.hom).obj u₀)
      (hx' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x' =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ)),
      eqToHom (congrArg Over.left hx').symm ≫
          ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map (eqToHom h ≫ η)).left ≫
        eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)) := by
    intro x' h hx'
    subst h
    simpa using hη
  obtain ⟨c⟩ := nonempty_affineChart (s := D.B.inclusion.map V.hom) (iΛ := iΛ)
    (pointMap_mem_range (hv₀ := hu₀'))
  exact ⟨l, inferInstance, inferInstance, inferInstance, inferInstance, hkl, hsep, V, g, hgsm,
    locallyOfFiniteType_of_isSmooth_schemeStack D.B D.S D.hS D.𝒳 D.locallyFiniteType V g hgsm,
    u₀', hu₀', hxₗ', eqToHom hobj ≫ η, key _ hobj hxₗ', ⟨c⟩, hsurj,
    surjective_residueFieldMap_of_surjective_ringMap _ c (range_pointMap c) (hsurj c)⟩

end AlgebraicGeometry.Stack
