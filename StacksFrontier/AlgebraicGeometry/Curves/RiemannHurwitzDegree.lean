module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GenericPointSupport
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CokernelSupportDegree
public import StacksFrontier.AlgebraicGeometry.Curves.RiemannHurwitzLocal
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional

/-!
# Degrees in the Riemann–Hurwitz formula

Let `0 → ℒ₁ → ℒ₂ → 𝒬 → 0` be a short exact sequence of modules on a proper scheme of dimension at
most one over a field `k`, with `ℒ₁`, `ℒ₂` finite locally free of rank one and `𝒬` coherent with
zero-dimensional support. Then `deg(ℒ₂) = deg(ℒ₁) + dim_k H⁰(X, 𝒬)`. For a generically étale
morphism `f : X → Y` of smooth proper curves this is applied to
`0 → f^*Ω_{Y/k} → Ω_{X/k} → Ω_{X/Y} → 0`.

## Main results

* `AlgebraicGeometry.curveDegree_eq_add_finrank_of_shortExact`: the degree identity above.
* `AlgebraicGeometry.mono_of_ne_zero_of_isTorsionFree`: a nonzero map from an invertible module to
  a torsion-free module on an integral scheme is injective.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_one_relativeDifferentials`: `Ω_{X/k}` is
  invertible for a smooth curve `X` over `k`.
* `AlgebraicGeometry.curveDegree_relativeDifferentials_eq_add_finrank`:
  `deg(Ω_{X/k}) = deg(f^*Ω_{Y/k}) + dim_k H⁰(X, Ω_{X/Y})` for a generically étale morphism of
  smooth curves with `X` proper.

## References

* [Stacks Project, Tag 0C1D](https://stacks.math.columbia.edu/tag/0C1D)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The degree jumps by the length of a zero-dimensional cokernel.** For a short exact
sequence `0 → ℒ₁ → ℒ₂ → 𝒬 → 0` on a proper scheme of dimension at most one over `k`, with `ℒ₁`
and `ℒ₂` finite locally free of rank one and `𝒬` coherent with support of dimension at most zero,
`deg(ℒ₂) = deg(ℒ₁) + dim_k H⁰(X, 𝒬)`: the degrees are Euler characteristics shifted by
`χ(𝒪_X)`, the Euler characteristic is additive ([Stacks, Tag 08AA]), and
`χ(𝒬) = dim_k H⁰(X, 𝒬)` ([Stacks, Tag 0AYT] (4)). -/
theorem curveDegree_eq_add_finrank_of_shortExact (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ 1]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ 1] [S.X₃.IsCoherent]
    (h₃ : topologicalKrullDim (_root_.SheafOfModules.supp S.X₃) ≤ 0) :
    curveDegree k p hdim S.X₂ 1 =
      curveDegree k p hdim S.X₁ 1 + Module.finrank k (cohomologyOverField k p S.X₃ 0) := by
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k p
    S.X₁ 1
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k p
    S.X₂ 1
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k p
  rw [curveDegree_eq_eulerCharacteristic_sub, curveDegree_eq_eulerCharacteristic_sub,
    eulerCharacteristic_add_of_shortExact k p hS,
    eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero k p S.X₃ h₃]
  ring

section Integral

open Stacks.ModuleStalk Opposite

variable {X : Scheme.{u}} [IsIntegral X]

/-- **A morphism into a torsion-free module on an integral scheme is determined by its stalk at
the generic point**, the germ maps of a torsion-free quasi-coherent module at the generic point
being injective. -/
theorem eq_zero_of_mapFun_genericPoint_eq_zero_of_isTorsionFree {N M : X.Modules}
    [M.IsQuasicoherent] (hM : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree M)
    (φ : N ⟶ M) (h : ∀ a, mapFun φ (genericPoint X) a = 0) : φ = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext t
  by_cases hV : Nonempty V.unop
  · have hη : genericPoint X ∈ V.unop :=
      ((genericPoint_spec X).mem_open_set_iff V.unop.isOpen).mpr (by simpa using hV)
    apply injective_generic_germ_of_isTorsionFree M hM hη
    have h1 := (mapFun_germ φ (genericPoint X) V.unop hη t).symm.trans
      (h ((N.presheaf.germ V.unop (genericPoint X) hη).hom t))
    exact h1.trans (map_zero _).symm
  · let underlying : TopCat.Sheaf Ab.{u} X.toTopCat := ⟨M.presheaf, M.isSheaf⟩
    exact TopCat.Presheaf.section_ext underlying V.unop (φ.val.app V t) 0 fun x hx =>
      False.elim (hV ⟨⟨x, hx⟩⟩)

/-- **A nonzero morphism from an invertible module to a torsion-free module on an integral
locally Noetherian scheme is a monomorphism.** Its kernel `𝒦` is a submodule of the torsion-free
module `𝒩`; the stalk `𝒩_η` at the generic point is a line over the function field on which the
stalk of the morphism is nonzero, so `𝒦_η = 0`, and a torsion-free module vanishing at the
generic point is zero. -/
theorem mono_of_ne_zero_of_isTorsionFree [IsLocallyNoetherian X] {N M : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] [M.IsQuasicoherent]
    (hM : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree M)
    (φ : N ⟶ M) (hφ : φ ≠ 0) : Mono φ := by
  refine Preadditive.mono_of_kernel_zero ?_
  have hK : genericPoint X ∉ SheafOfModules.supp (kernel φ) := by
    rintro ⟨a₀, ha⟩
    let a : TopCat.Presheaf.stalk (C := Ab.{u}) (kernel φ).presheaf (genericPoint X) := a₀
    let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
    have hinj : Function.Injective (mapFun (kernel.ι φ) (genericPoint X)) :=
      TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
        (f := (kernel.ι φ).mapPresheaf)
        (fun U => Scheme.Modules.injective_app_of_mono (kernel.ι φ) U) (genericPoint X)
    have hb : mapFun (kernel.ι φ) (genericPoint X) a ≠ 0 := fun h0 =>
      ha (hinj (h0.trans (map_zero _).symm))
    have hrank :=
      Stacks.AlgebraicGeometry.ReflexiveModules.finrank_stalk_genericPoint_eq_one_of_isInvertible N
    have hspan := (finrank_eq_one_iff_of_nonzero' _ hb).mp hrank
    apply hφ
    refine eq_zero_of_mapFun_genericPoint_eq_zero_of_isTorsionFree hM φ fun c => ?_
    obtain ⟨r, hr⟩ := hspan c
    rw [← hr, mapFun_smul, ← mapFun_comp, kernel.condition]
    obtain ⟨U, hxU, t, ht⟩ := TopCat.Presheaf.exists_germ_eq _ a
    rw [← ht, mapFun_germ]
    simp
  have := isCoherent_of_isInvertible' N
  have : N.IsQuasicoherent := isQuasicoherent_of_isCoherent N
  have : (kernel φ).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel φ
  exact (isZero_of_mono_of_genericPoint_notMem (kernel.ι φ) hK).eq_of_src _ _

end Integral

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [IsCurve k pX]
  [Smooth pX]

/-- **The sheaf of differentials of a smooth curve over a field is finite locally free of rank
one** ([Stacks, Tag 02G1]): it is finite locally free, and its rank at the generic point is the
dimension of the curve. -/
theorem isFiniteLocallyFreeOfRank_one_relativeDifferentials :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials pX) 1 := by
  have := pX.isFiniteLocallyFree_relativeDifferentials
  have : (Scheme.Hom.relativeDifferentials pX).IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentKernel.isQuasicoherent_isFiniteType_of_isFiniteLocallyFree
      (F := Scheme.Hom.relativeDifferentials pX)).2
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq _ 1 (genericPoint X) ?_
  rw [Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk]
  exact finrank_stalk_relativeDifferentials_eq_one pX (genericPoint X)

end Curve

section Morphism

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k))
  (pY : Y ⟶ Spec (.of k)) [IsCurve k pX] [IsCurve k pY] [Smooth pX] [Smooth pY] [IsProper pX]
  (f : X ⟶ Y) (hf : f ≫ pY = pX)

/-- **`deg(Ω_{X/k}) = deg(f^*Ω_{Y/k}) + dim_k H⁰(X, Ω_{X/Y})`** for a morphism `f : X → Y` of
smooth curves over `k`, with `X` proper, whose differential `f^*Ω_{Y/k} → Ω_{X/k}` is nonzero
(condition (1) of [Stacks, Tag 0C1C]). The sequence `0 → f^*Ω_{Y/k} → Ω_{X/k} → Ω_{X/Y} → 0` is
exact ([Stacks, Tag 01UX]; on the left because a nonzero map of invertible modules on an integral
scheme is injective), and `Ω_{X/Y}` is supported on finitely many closed points. -/
theorem curveDegree_relativeDifferentials_eq_add_finrank
    (hdf : Scheme.Hom.relativeDifferentialsMap f pY pX (𝟙 (Spec (.of k)))
      (by simpa using hf) ≠ 0) :
    letI := isFiniteLocallyFreeOfRank_one_relativeDifferentials pX
    letI := isFiniteLocallyFreeOfRank_one_relativeDifferentials pY
    letI := isFiniteLocallyFreeOfRank_pullback f (Scheme.Hom.relativeDifferentials pY) 1
    curveDegree k pX (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := pX)))
        (Scheme.Hom.relativeDifferentials pX) 1 =
      curveDegree k pX (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := pX)))
          ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials pY)) 1 +
        Module.finrank k (cohomologyOverField k pX (Scheme.Hom.relativeDifferentials f) 0) := by
  subst hf
  let := isFiniteLocallyFreeOfRank_one_relativeDifferentials (f ≫ pY)
  let := isFiniteLocallyFreeOfRank_one_relativeDifferentials pY
  let := isFiniteLocallyFreeOfRank_pullback f (Scheme.Hom.relativeDifferentials pY) 1
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ pY)
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (f ≫ pY)
  have hdim : topologicalKrullDim X ≤ 1 :=
    le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f ≫ pY))
  obtain ⟨hzero, hexact⟩ := Scheme.Hom.toRelativeDifferentials_exact f pY
  let df := Scheme.Hom.relativeDifferentialsMap f pY (f ≫ pY) (𝟙 (Spec (.of k)))
    (Category.comp_id (f ≫ pY)).symm
  let S : ShortComplex X.Modules :=
    ShortComplex.mk df (Scheme.Hom.toRelativeDifferentials f pY) hzero
  -- the target `Ω_{X/k}` is torsion free and the source is invertible
  have hΩc : (Scheme.Hom.relativeDifferentials (f ≫ pY)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (f ≫ pY) _ 1
  have hΩq : (Scheme.Hom.relativeDifferentials (f ≫ pY)).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have htf : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree
      (Scheme.Hom.relativeDifferentials (f ≫ pY)) :=
    (isTorsionFree_iff_isFiniteLocallyFree (isRegular_of_smooth_over_field (f ≫ pY)) hdim
      _).mpr ((f ≫ pY).isFiniteLocallyFree_relativeDifferentials)
  have hinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials pY)) :=
    Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one X _ inferInstance
  have hmono : Mono df := mono_of_ne_zero_of_isTorsionFree htf df hdf
  have hS : S.ShortExact :=
    { exact := hexact
      mono_f := hmono
      epi_g := Scheme.Hom.toRelativeDifferentials_epi f pY }
  -- the cokernel `Ω_{X/Y}` is coherent and supported in dimension zero
  have hQq : (Scheme.Hom.relativeDifferentials f).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentials f
  have : (Scheme.Hom.relativeDifferentials f).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent'_of_isQuasicoherent_of_isFiniteType _
  have hη : genericPoint X ∉ SheafOfModules.supp (Scheme.Hom.relativeDifferentials f) :=
    (exists_proper_closed_supset_supp_iff_genericPoint_notMem _).mp
      (((genericallyEtale_tfae (f ≫ pY) pY f rfl).out 1 2).mp hdf)
  have h₃ := topologicalKrullDim_supp_le_zero_of_genericPoint_notMem hdim
    (Scheme.Hom.relativeDifferentials f) inferInstance hη
  exact curveDegree_eq_add_finrank_of_shortExact k (f ≫ pY) hdim S hS h₃

end Morphism

end AlgebraicGeometry

end
