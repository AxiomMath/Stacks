module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesChart
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# Smoothness of a 1-morphism out of an algebraic space is étale local on the source

Let `y : Y ⟶ 𝒳'` be a 1-morphism from the stack of an algebraic space to an algebraic stack and
`{e_k : A_k ⟶ Y}` an étale covering. If every `y ∘ e_k` is smooth, so is `y`.

This is the step of Stacks 0CJU which checks that the glued 1-morphism `x' : U' ⟶ 𝒳'` of a glued
smooth lift is smooth: it is smooth on the members of an étale covering of `U'`.

## Main results

* `AlgebraicGeometry.Stack.isSmooth_of_isEtaleCovering`: the statement above.

## Implementation notes

Smoothness of 1-morphisms of algebraic stacks is the existential smooth-diagram test of
Stacks 06FM. The diagram used is the 2-fibre product `Z = Y ×_{𝒳'} Y₀` with a smooth surjective
chart `Y₀ ⟶ 𝒳'` of the target: its projection to `Y` is smooth and surjective, and its
projection `q` to `Y₀` is smooth because smoothness of morphisms of algebraic spaces is checked
on smooth neighbourhoods of points (Stacks 06F8), and `Z ×_Y A_k ⟶ Z` is an étale neighbourhood
of a point on which `q` is the projection of the 2-fibre product `A_k ×_{𝒳'} Y₀`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Smoothness of a 1-morphism out of an algebraic space is étale local on the source.** If
`{e_k : A_k ⟶ Y}` is an étale covering and every `y ∘ e_k` is smooth, then `y` is smooth. -/
theorem isSmooth_of_isEtaleCovering {𝒳' : AlgebraicStacks.{u, w} B S hS}
    {Y : AlgebraicSpaces B S hS} (y : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Y ⟶ 𝒳')
    {K : Type v} {A : K → AlgebraicSpaces B S hS} (e : ∀ k, A k ⟶ Y)
    (he : Space.IsEtaleCovering B S hS (fun k => (A k).obj) (fun k => (e k).hom))
    (hy : ∀ k, AlgebraicStacks.IsSmooth B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ≫ y)) :
    AlgebraicStacks.IsSmooth B S hS y := by
  obtain ⟨U₀, b, hb, hbs⟩ := exists_smooth_surjective_spaceChart 𝒳'
  let Y₀ : AlgebraicSpaces B S hS := ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩
  obtain ⟨Z, p, q, γ, ⟨hZ⟩, hp, hps⟩ := exists_smooth_surjective_twoFibreProduct (U := Y₀) y b
    (isRelativelySmooth_of_isSmooth_space_source b hb)
    (hasRelativeProperty_surjective_of_space_source b hbs)
  have hq : Space.IsSmooth B S hS q.hom := by
    refine ((Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      |>.iff_forall_exists_smooth_neighborhood Z.property Y₀.property q.hom).2 fun z => ?_
    have hz : Space.pointsMap B S hS Z.obj p.hom z ∈
        (⋃ k, Set.range (Space.pointsMap B S hS (A k).obj (e k).hom)) := by
      rw [he.jointly_surjective]
      exact Set.mem_univ _
    obtain ⟨k, a, ha⟩ := Set.mem_iUnion.1 hz
    let P := AlgebraicSpaces.fiberProduct B S hS p (e k)
    let pf : P ⟶ Z := ObjectProperty.homMk (pullback.fst p.hom (e k).hom)
    let ps : P ⟶ A k := ObjectProperty.homMk (pullback.snd p.hom (e k).hom)
    have hP : IsPullback pf ps p (e k) := AlgebraicSpaces.isPullback_fiberProduct B S hS p (e k)
    obtain ⟨w, hw, -⟩ := Space.exists_point_of_isPullback B S hS hP z a ha.symm
    have hpf : Space.IsEtale B S hS pf.hom :=
      Space.isEtale_of_isPullback_of_isAlgebraicSpace B S hS
        (AlgebraicSpaces.isPullback_hom B S hS hP) P.property Z.property (A k).property
        Y.property (he.etale k)
    let T : TwoCommSq ((algebraicSpaceStackFunctor.{u, w} B S hS).map p)
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map (e k)) :=
      algebraicSpaceStackSquare.{u, w} B S hS Z.property (A k).property Y.property P.property
        (p := pf.hom) (q := ps.hom) (a := p.hom) (b := (e k).hom)
        (AlgebraicSpaces.isPullback_hom B S hS hP).w
    have hT : IsTwoFibreProduct T :=
      isTwoFibreProduct_algebraicSpaceStackSquare.{u, w} B S hS Z.property (A k).property
        Y.property P.property (p := pf.hom) (q := ps.hom) (a := p.hom) (b := (e k).hom)
        (AlgebraicSpaces.isPullback_hom B S hS hP)
    have hsm : Space.IsSmooth B S hS (pf ≫ q).hom :=
      isSmooth_fst_of_isTwoFibreProduct_of_isRelativelySmooth (p := pf ≫ q) (q := ps)
        (γ := ((⟨_, _, _, γ⟩ : TwoCommSq y b).swap.paste T).iso)
        (isTwoFibreProduct_paste (isTwoFibreProduct_swap hZ) hT)
        (isRelativelySmooth_of_isSmooth_space_source _ (hy k))
    exact ⟨P.obj, Y₀.obj, P.property, Y₀.property, pf.hom, 𝟙 _, (pf ≫ q).hom, w,
      Space.isSmooth_of_isEtale B S hS Z.property hpf, Space.isSmooth_id B S hS Y₀.property, hw,
      by simp, hsm⟩
  exact ⟨Z.obj, Y₀.obj, Z.property, Y₀.property,
    ((algebraicSpaceStackFunctor.{u, w} B S hS).map p).hom, b.hom, q.hom,
    ⟨(InducedBicategory.isoHom γ).symm⟩,
    isRelativelySmooth_associatedMap B S hS Z.property Y.property p.hom hp,
    isSurjectiveOnObjects_associatedMap B S hS Z.property Y.property p.hom hps,
    isRelativelySmooth_of_isSmooth_space_source b hb, hq⟩

end AlgebraicGeometry.Stack
