module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackLiftCore

/-!
# The lifting step for a stack, from a lifted chart point over a covering

The variant of `AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_lift_of_chartPoint` in which
the chart algebra `P` need not be formally smooth over `A'`: the chart point `ū` over `C' ⧸ I C'`
comes with a given lift `u₀ : P → C'`
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_lift_of_chartPoint_of_lift`). This is the
shape of the lifting step in Stacks 0DNU, where the object over `C'` is given.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_lift_of_chartPoint_of_lift`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe w u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}

namespace StackChart

variable (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) {C' : Type u} [CommRing C']
  [Algebra (ringOf B S hS T') C'] (hC : Cardinal.mk C' < B.cutoff) (I : Ideal (ringOf B S hS T'))
  (hI : I ^ 2 = ⊥)

/-- The chart data of the lifting problem as a datum along the nerve, with a given lift of the
point. -/
noncomputable def chartNerveDatumOfLift {xb : 𝒳.val.obj}
    (ubar : P.obj →ₐ[ringOf B S hS T'] (red I (descNerve T' hC 0)).obj) (c : ξ a ι ubar ⟶ xb)
    [𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) c]
    (u₀ : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
    (hu₀ : (thk I hI (descNerve T' hC 0)).q.hom.hom.comp u₀ = ubar) :
    NerveDatum B.aleph0_lt_cutoff C' hC I hI (stackGroupoid a ι) where
  ubar := ubar
  u₀ := u₀
  u₀_lift := hu₀
  rbar := chartRbar (hA := hA) hC I ubar c
  src_rbar := rfl
  tgt_rbar := rfl
  norm_rbar := chartRbar_norm hC I ubar c

/-- **The lifting step for a stack from a lifted chart point over a covering.** -/
theorem exists_lift_of_chartPoint_of_lift
    (h𝒳 : 𝒳.val.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS))
    [Module.FaithfullyFlat (ringOf B S hS T') C'] [Algebra.FinitePresentation (ringOf B S hS T') C']
    [Module.FinitePresentation P.obj Ω[P.obj⁄ringOf B S hS T']]
    (hG : (stackGroupoid a ι).SrcFormallySmooth)
    {Q : Type u} [CommRing Q] [Algebra (ringOf B S hS T') Q]
    [Module.FinitePresentation Q Ω[Q⁄ringOf B S hS T']]
    (b : Chart (stackArr a ι) Q) (hb : b.IsFormallyEtale) (sV tV : P.obj →ₐ[ringOf B S hS T'] Q)
    (hsV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).src = v.comp sV)
    (htV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).tgt = v.comp tV)
    {xb : 𝒳.val.obj} (hxb : 𝒳.val.p.obj xb = specOver (red I (baseAlg (κ := B.cutoff) hA)))
    (ubar : P.obj →ₐ[ringOf B S hS T'] (red I (descNerve T' hC 0)).obj) (c : ξ a ι ubar ⟶ xb)
    (hc : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) c)
    (εbar : Q →ₐ[ringOf B S hS T'] (red I (descNerve T' hC 0)).obj)
    (hε : b.app _ εbar = Arr.idt ubar) (u₀ : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
    (hu₀ : (thk I hI (descNerve T' hC 0)).q.hom.hom.comp u₀ = ubar) :
    ∃ (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj) (x' : 𝒳.val.obj)
      (ζ : ξ a ι u ⟶ x') (φ : xb ⟶ x'),
      𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ ∧
        𝒳.val.p.IsHomLift (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) φ := by
  have := hc
  let D := chartNerveDatumOfLift hA hC I hI ubar c u₀ hu₀
  have hcoc : D.IsCocycle := chartRbar_cocycle hC I ubar c
  obtain ⟨ε₀, ⟨hε₀, -⟩, -⟩ := hb _ _ (thk I hI (descNerve T' hC 0)).q
    (thk I hI (descNerve T' hC 0)).surj (thk I hI (descNerve T' hC 0)).sq εbar (Arr.idt D.u₀)
    ((Arr.map_idt _ _).trans ((congrArg Arr.idt D.u₀_lift).trans hε.symm))
  obtain ⟨u, hu, r, hrq, hs, ht, hcocy⟩ := NerveDatum.exists_lift_arrow_cocycle (D := D)
    (sV := sV) (tV := tV) (εbar := εbar) (hsV := hsV) (htV := htV) (hε := hε) (hb := hb)
    (ε₀ := ε₀) (hε₀ := hε₀) hG hcoc
  obtain ⟨src, tgt, hom, lift⟩ := r
  change src = _ at hs
  change tgt = _ at ht
  subst hs ht
  change (qC hC I hI).hom.hom.comp u = ubar at hu
  subst hu
  obtain ⟨_, hcocy⟩ := hcocy
  obtain ⟨x', ζ, hζl, hζ⟩ := exists_descent_of_hom hA u hom h𝒳 hcocy
  have hx' : 𝒳.val.p.obj x' = specOver (baseAlg (κ := B.cutoff) hA) :=
    @IsHomLift.codomain_eq _ _ _ _ 𝒳.val.p _ _ _ _
      (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ hζl
  have := hζl
  have hζ' : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫
      specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) (trans a ι (qC hC I hI) u ≫ ζ) :=
    isHomLift_of_eq (spec_baseMap_q hA hC I hI) inferInstance
  have hρ := Arr.hom_eq_of_eq hrq.symm
  obtain ⟨φ, hφ, -⟩ := exists_hom_of_chart (baseThk B.aleph0_lt_cutoff hC hI hA).bot (rV₀ hC I)
    (rVₗ hC I) h𝒳 (isPullback_specOverMap_of_isPushout _ _ _ _
      (isPushout_red_nerve_one B.aleph0_lt_cutoff C' hC I hI hA)) (ofArrows_red_mem hA hC I hI)
    (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) hxb hx' _ c hc
    (trans a ι (qC hC I hI) u ≫ ζ) hζ' (chartRbar hC I _ c).hom (chartRbar hC I _ c).lift
    (chartRbar_fac hC I _ c) (red_descArr_fac u hom ζ hζ _ _ _ hρ)
  exact ⟨u, x', ζ, φ, hζl, hφ⟩

end StackChart

end AlgebraicGeometry.Stack.GroupoidLift

end
