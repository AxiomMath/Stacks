module

public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullbackRigidity
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Stack.SquareCocone
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge

/-!
# Rigidity of points along a smooth surjective affine chart

Let `f : 𝒰 ⟶ 𝒳` be a flat, locally finitely presented, surjective 1-morphism of algebraic stacks
and `y` an object of `𝒳`.  Every terminal arrow `t : f(x₀) ⟶ y` of `f` (a terminal object of
`CostructuredArrow f y`) is left cancellable in `𝒳`: the point form of Stacks 06QA gives an fppf
covering of the base of `y` along which `y` lifts to `𝒰`, every such lift factors through `t`,
and arrows out of `y` are determined on a covering since `𝒳` is a stack.

This is the separation input `hsep` of the rigidity theorem
`AlgebraicGeometry.Stack.AlgebraicStacks.eq_of_pointPullbackTransportIso_eq`; together with the
detection of arrows by the structure sheaf of a scheme it gives rigidity for an affine, smooth and
surjective chart `U ⟶ 𝒳` by a scheme, with no further hypothesis.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.cancel_of_isTerminal_costructuredArrow`: terminal
  arrows of a flat, locally finitely presented, surjective 1-morphism are left cancellable.
* `AlgebraicGeometry.Stack.AlgebraicStacks.eq_of_pointPullbackTransportIso_eq_of_isSmooth`:
  rigidity of points along an affine, smooth, surjective chart by a scheme.

## References

* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Terminal arrows of a flat, locally finitely presented, surjective 1-morphism are left
cancellable.**  Let `f : 𝒰 ⟶ 𝒳` be a flat, locally finitely presented, surjective 1-morphism of
algebraic stacks and `t : f(x₀) ⟶ y` a terminal object of `CostructuredArrow f y`.  Two arrows
`φ₁ φ₂ : y ⟶ y'` with `t ≫ φ₁ = t ≫ φ₂` are equal: `y` lifts to `𝒰` along an fppf covering of its
base (the point form of Stacks 06QA), each lift factors through `t`, and arrows out of `y` that
agree on a covering are equal in a stack. -/
theorem cancel_of_isTerminal_costructuredArrow {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒰 ⟶ 𝒳) (hflat : IsFlat B S hS f) (hlfp : IsLocallyOfFinitePresentation B S hS f)
    (hsurj : IsSurjective B S hS f) {y : 𝒳.val.val.obj}
    (t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y) (ht : IsTerminal t)
    {y' : 𝒳.val.val.obj} (φ₁ φ₂ : y ⟶ y') (h : t.hom ≫ φ₁ = t.hom ≫ φ₂) : φ₁ = φ₂ := by
  classical
  let p := 𝒳.val.val.p
  let U := p.obj y
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  have hlift : ∀ z : ULift.{u + 1} ((BigFppfOver.toScheme B S hS).obj U),
      ∃ (T : B.Schemes) (m : T ⟶ U.left),
        Flat (B.inclusion.map m) ∧ LocallyOfFinitePresentation (B.inclusion.map m) ∧
        z.down ∈ Set.range (B.inclusion.map m) ∧
        ∃ (x : 𝒰.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y),
          p.IsHomLift (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
    intro z
    obtain ⟨T, m, h₁, h₂, h₃, x, α, hα⟩ := exists_scheme_lift_of_isFlat_isLfp_at_point B S hS f
      hflat hlfp U ⟨y, rfl⟩ ((pointsHomeomorphScheme B S hS U).symm z.down) (hsurj _)
    exact ⟨T, m, h₁, h₂, by rwa [Homeomorph.apply_symm_apply] at h₃, x, α, hα⟩
  choose T m hfl hlf hz x α hα using hlift
  let V₁ : ULift.{u + 1} ((BigFppfOver.toScheme B S hS).obj U) → BigFppfOver B S hS :=
    fun i ↦ Over.mk (m i ≫ U.hom)
  let e : ∀ i, V₁ i ⟶ U := fun i ↦ Over.homMk (m i) rfl
  have he : Sieve.ofArrows V₁ e ∈ BigFppfOver.topology B S hS U :=
    mem_topology_of_family B S hS T m hfl hlf (fun z ↦ ⟨⟨z⟩, hz ⟨z⟩⟩)
  -- each lift factors through the terminal arrow `t`
  have hα₁₂ : ∀ i, α i ≫ φ₁ = α i ≫ φ₂ := fun i ↦ by
    have hw : _ ≫ t.hom = α i := CostructuredArrow.w (ht.from (CostructuredArrow.mk (α i)))
    rw [← hw, Category.assoc, Category.assoc, h]
  -- the two arrows lie over the same morphism of the site, by subcanonicity
  have hbase : p.map φ₁ = p.map φ₂ := by
    refine (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := BigFppfOver.topology B S hS) (yoneda.obj (p.obj y')) _ he).isSeparatedFor.ext
      fun W g hg ↦ ?_
    obtain ⟨_, k, _, ⟨i⟩, rfl⟩ := hg
    have h₁ : p.IsHomLift (e i ≫ p.map φ₁) (α i ≫ φ₁) := inferInstance
    have h₂ : p.IsHomLift (e i ≫ p.map φ₂) (α i ≫ φ₁) := by
      rw [hα₁₂ i]
      infer_instance
    show (k ≫ e i) ≫ p.map φ₁ = (k ≫ e i) ≫ p.map φ₂
    rw [Category.assoc, Category.assoc]
    exact congrArg (k ≫ ·) ((@IsHomLift.fac _ _ _ _ p _ _ _ _ _ _ h₁).trans
      (@IsHomLift.fac _ _ _ _ p _ _ _ _ _ _ h₂).symm)
  obtain ⟨hfib, ⟨hst, -⟩, -⟩ := 𝒳.property
  have hp : p.IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS) :=
    hst.isStackInGroupoids hfib
  have : p.IsHomLift (p.map φ₁) φ₂ := by
    rw [hbase]
    infer_instance
  exact Functor.IsStackInGroupoids.hom_ext_of_cover hp e he
    (fun k l ↦ pullback.fst (e k) (e l)) (fun k l ↦ pullback.snd (e k) (e l))
    (fun k l ↦ IsPullback.of_hasPullback (e k) (e l)) (p.map φ₁) rfl α rfl hα₁₂

/-- **Rigidity of points along a smooth surjective affine chart.**  Let `f : U ⟶ 𝒳` be an affine,
smooth and surjective 1-morphism from (the algebraic stack of) a scheme `U` to an algebraic
stack `𝒳`.  Then a 2-arrow between points of `𝒳` over an affine scheme is determined by the
isomorphism of tensor functors it induces: if `a, b : x ≅ y` induce the same `f_x^* ≅ f_y^*`,
then `a = b`.  The module detecting the 2-arrow is the direct image `f_* 𝒪_U`. -/
theorem eq_of_pointPullbackTransportIso_eq_of_isSmooth (U : BigFppfOver B S hS)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hf : IsAffineHom B S hS f) (hsm : IsSmooth B S hS f) (hsurj : IsSurjective B S hS f)
    {R : Type u} [CommRing R] {x y : 𝒳.val.val.obj}
    (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R))
    (ey : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) ≅ Spec (CommRingCat.of R))
    (a b : x ≅ y)
    (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫ ey.hom = e.hom)
    (hb : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map b.hom) ≫ ey.hom = e.hom)
    (h : pointPullbackTransportIso B S hS 𝒳 e ey a ha =
      pointPullbackTransportIso B S hS 𝒳 e ey b hb) : a = b :=
  eq_of_pointPullbackTransportIso_eq B S hS f hf
    ⟨SheafOfModules.unit _, SheafOfModules.isQuasicoherentOnSite_unit _⟩
    (fun _ _ k₁ k₂ _ hu' hk ↦ schemeStack_hom_ext_of_structureSheaf_map_eq.{u, w} B S hS U k₁ k₂
      hu' hk)
    (fun _ t ht _ φ₁ φ₂ hc ↦ cancel_of_isTerminal_costructuredArrow B S hS f
      (isFlat_of_isSmooth B S hS f hsm) (isLocallyOfFinitePresentation_of_isSmooth B S hS f hsm)
      hsurj t ht φ₁ φ₂ hc)
    e ey a b ha hb h

end AlgebraicGeometry.Stack.AlgebraicStacks
