module

public import Mathlib.RingTheory.Flat.Equalizer
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSmoothPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInEtaleBaseChange

/-!
# Integral closedness of the structure sheaf in a direct image, under smooth base change

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g-->  Y
```

be a cartesian square of algebraic spaces over a scheme `S` of a big fppf site `B`, with `f`
quasi-compact and quasi-separated and `g` smooth.  If the structure sheaf of `Y` is integrally
closed in `f_* 𝒪_X` (`AlgebraicGeometry.Space.AlgebraSheaf.IsIntegrallyClosed`: on every étale
chart the structure-algebra map is injective with image the locally integral sections), then the
structure sheaf of `Y'` is integrally closed in `f'_* 𝒪_{X'}`.  This is the step of the proof of
Stacks 082F that combines Stacks 073K (the degree-zero flat base change for `f_* 𝒪_X`) with
Stacks 082E (the integral closure commutes with smooth pullback); it is the smooth analogue of
the étale step `AlgebraicGeometry.Space.isRelativeNormalization_of_isPullback_of_isEtale` behind
part (1) of Stacks 0ABP.

## Main results

* `Stacks.injective_and_isIntegral_mem_range_of_tensor_equalizer`: the commutative algebra of the
  chartwise step — an equalizer presentation of `A₀` over `R`, base changed along a smooth
  `R ⟶ S`, carries "`R` is integrally closed in `A₀`" to "`S` is integrally closed in `A₁`".
* `AlgebraicGeometry.Space.chartDiagramSectionsHom`: the projection of the sections of `f_* 𝒪_X`
  over an étale chart `V` of `Y` to the functions on an étale chart of `X` above `X ×_Y V`, as a
  ring homomorphism.
* `AlgebraicGeometry.Space.AlgebraSheaf.isIntegrallyClosed_of_hasAffineChartDiagram`: integral
  closedness of a quasi-coherent algebra sheaf may be checked on the charts carrying an affine
  chart diagram over a morphism.
* `AlgebraicGeometry.Space.isIntegrallyClosed_chart_of_isPullback_of_isSmooth`: the statement
  over a diagram of affine charts over `g`.
* `AlgebraicGeometry.Space.isIntegrallyClosed_pushforwardAlgebra_of_isPullback_of_isSmooth`:
  the statement above.

## Implementation notes

Over an affine chart diagram `U ⟶ V` over `g`, with `R = 𝒪(V)` and `S = 𝒪(U)` (a smooth
`R`-algebra), choose an affine chart `W` of `X` covering `V ×_Y X` and an affine chart `R'` of
`X` covering the relation `W ×_{V ×_Y X} W`
(`AlgebraicGeometry.Space.exists_affine_presentation_chartBaseChange`).  The sections `A₀` of
`f_* 𝒪_X` over `V` embed into `𝒪(W)` with image the equalizer of the two restrictions to
`𝒪(R')`; the sections `A₁` of `f'_* 𝒪_{X'}` over `U` embed into `𝒪(W ×_V U) = S ⊗_R 𝒪(W)` and
land in the equalizer of the two restrictions to `𝒪(R' ×_V U) = S ⊗_R 𝒪(R')`.  An element of
`A₁` integral over `S` therefore lies, `S` being flat over `R`, in `S ⊗_R A₀`, and is integral
over `S` there; since `R` is integrally closed in `A₀`, Stacks 03GG
(`Stacks.isIntegral_iff_mem_range_lTensor`) puts it in the image of `S`.  This needs only the
injectivity of `A₁ ⟶ 𝒪(W ×_V U)`, not the identification `A₁ = S ⊗_R A₀` of Stacks 073K
itself.

## References

* [Stacks Project, Tag 082F](https://stacks.math.columbia.edu/tag/082F)
* [Stacks Project, Tag 082E](https://stacks.math.columbia.edu/tag/082E)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03GG](https://stacks.math.columbia.edu/tag/03GG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace Stacks

/-- **Integral closedness under a smooth base change, through equalizer presentations.**  Let
`S` be a smooth `R`-algebra and let `A₀` be an `R`-algebra in which `R` is integrally closed
(the structure map is injective, and every element integral over `R` comes from `R`).  Present
`A₀` as the equalizer of two `R`-algebra maps `α, β : C ⟶ D` through an injection `ι`, and let
`C' ≃ S ⊗_R C`, `D' ≃ S ⊗_R D` carry the base changes `α', β'` of `α, β`.  If an `S`-algebra
`A₁` embeds into `C'` by some `ι'` landing in the equalizer of `α'` and `β'`, then `S` is
integrally closed in `A₁`. -/
theorem injective_and_isIntegral_mem_range_of_tensor_equalizer
    {R S A₀ C D A₁ C' D' : Type*} [CommRing R] [CommRing S] [CommRing A₀] [CommRing C]
    [CommRing D] [CommRing A₁] [CommRing C'] [CommRing D'] [Algebra R S] [Algebra.Smooth R S]
    [Algebra R A₀] [Algebra R C] [Algebra R D] [Algebra S A₁] [Algebra S C'] [Algebra S D']
    (α β : C →ₐ[R] D) (ι : A₀ →ₐ[R] C) (hι : Function.Injective ι)
    (heq : ∀ c, α c = β c → c ∈ Set.range ι)
    (h₀ : Function.Injective (algebraMap R A₀))
    (h₀' : ∀ a : A₀, IsIntegral R a → a ∈ Set.range (algebraMap R A₀))
    (eC : S ⊗[R] C ≃ₐ[S] C') (eD : S ⊗[R] D ≃ₐ[S] D') (α' β' : C' →ₐ[S] D')
    (hα : ∀ c, α' (eC (1 ⊗ₜ c)) = eD (1 ⊗ₜ α c)) (hβ : ∀ c, β' (eC (1 ⊗ₜ c)) = eD (1 ⊗ₜ β c))
    (ι' : A₁ →ₐ[S] C') (hι' : Function.Injective ι') (hab : ∀ x, α' (ι' x) = β' (ι' x)) :
    Function.Injective (algebraMap S A₁) ∧
      ∀ x : A₁, IsIntegral S x → x ∈ Set.range (algebraMap S A₁) := by
  -- the base change of an algebra map `γ`, read through `eC` and `eD`
  have hbase : ∀ (γ : C →ₐ[R] D) (γ' : C' →ₐ[S] D'),
      (∀ c, γ' (eC (1 ⊗ₜ c)) = eD (1 ⊗ₜ γ c)) →
        ∀ y, γ' (eC y) = eD (LinearMap.lTensor S γ.toLinearMap y) := by
    intro γ γ' hγ y
    induction y with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul s c =>
      have h1 : s ⊗ₜ[R] c = s • (1 ⊗ₜ[R] c : S ⊗[R] C) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have h2 : s ⊗ₜ[R] γ c = s • (1 ⊗ₜ[R] γ c : S ⊗[R] D) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.lTensor_tmul, h1, map_smul, map_smul, hγ]
      exact (congrArg eD h2).trans (map_smul _ _ _) |>.symm
  -- the base change of `ι` as an algebra map
  let ιS : S ⊗[R] A₀ →ₐ[S] S ⊗[R] C := Algebra.TensorProduct.map (AlgHom.id S S) ι
  have hιS : ∀ w, ιS w = LinearMap.lTensor S ι.toLinearMap w := by
    intro w
    induction w with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul s a => rfl
  have hιSinj : Function.Injective ιS := fun a b h =>
    Module.Flat.lTensor_preserves_injective_linearMap ι.toLinearMap hι (by rwa [hιS, hιS] at h)
  -- the base change of the structure map of `A₀`
  have hrange : ∀ w : S ⊗[R] A₀,
      w ∈ LinearMap.range (LinearMap.lTensor S (Algebra.linearMap R A₀)) →
        w ∈ Set.range (algebraMap S (S ⊗[R] A₀)) := by
    rintro w ⟨t, rfl⟩
    induction t with
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | tmul s r =>
      refine ⟨r • s, ?_⟩
      rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, ← mul_one (algebraMap R A₀ r),
        ← Algebra.smul_def, TensorProduct.smul_tmul]
  -- the structure map of `S ⊗[R] C` is injective, `S` being flat
  have hSC : Function.Injective (algebraMap S (S ⊗[R] C)) := by
    have hRC : Function.Injective (Algebra.linearMap R C) := by
      have : (Algebra.linearMap R C : R → C) = ι ∘ algebraMap R A₀ := by
        funext r; exact (ι.commutes r).symm
      rw [this]; exact hι.comp h₀
    have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := S) _ hRC
    intro s t hst
    have h1 : ∀ s : S, algebraMap S (S ⊗[R] C) s =
        LinearMap.lTensor S (Algebra.linearMap R C) (s ⊗ₜ 1) := fun s => by
      rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]; rfl
    rw [h1, h1] at hst
    have := hl hst
    simpa using congrArg (TensorProduct.rid R S) this
  have hcomp : ∀ s : S, ι' (algebraMap S A₁ s) = eC (algebraMap S (S ⊗[R] C) s) := fun s => by
    rw [AlgHom.commutes, AlgEquiv.commutes]
  refine ⟨fun s t hst => hSC (eC.injective ?_), fun x hx => ?_⟩
  · rw [← hcomp, ← hcomp, hst]
  -- an integral element of `A₁`
  set y := eC.symm (ι' x) with hy
  have hyeq : LinearMap.lTensor S α.toLinearMap y = LinearMap.lTensor S β.toLinearMap y := by
    apply eD.injective
    rw [← hbase α α' hα, ← hbase β β' hβ, hy, AlgEquiv.apply_symm_apply, hab]
  -- `y` comes from the equalizer
  obtain ⟨z, hz⟩ := (LinearMap.tensorEqLocusEquiv S S α.toLinearMap β.toLinearMap).surjective
    ⟨y, hyeq⟩
  have hz' : (LinearMap.eqLocus α.toLinearMap β.toLinearMap).subtype.lTensor S z = y := by
    have := congrArg Subtype.val hz
    rwa [LinearMap.tensorEqLocusEquiv_apply, LinearMap.tensorEqLocus_coe] at this
  -- the equalizer is the image of `ι`
  let φ : LinearMap.eqLocus α.toLinearMap β.toLinearMap →ₗ[R] A₀ :=
    (LinearEquiv.ofInjective ι.toLinearMap hι).symm.toLinearMap ∘ₗ
      Submodule.inclusion (fun c hc => heq c hc)
  have hφ : ι.toLinearMap ∘ₗ φ = (LinearMap.eqLocus α.toLinearMap β.toLinearMap).subtype := by
    ext c
    exact LinearEquiv.ofInjective_symm_apply (f := ι.toLinearMap) (h := hι) _
  set w := LinearMap.lTensor S φ z with hw
  have hyw : ιS w = y := by
    rw [hιS, hw, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hφ, hz']
  -- `w` is integral, so it is a scalar
  have hxint : IsIntegral S y := by
    rw [hy]
    exact (isIntegral_algHom_iff eC.symm.toAlgHom eC.symm.injective).2
      ((isIntegral_algHom_iff ι' hι').2 hx)
  have hwint : IsIntegral S w := by
    rw [← hyw] at hxint
    exact (isIntegral_algHom_iff ιS hιSinj).1 hxint
  have hι₀ : ∀ a : A₀, IsIntegral R a ↔ a ∈ LinearMap.range (Algebra.linearMap R A₀) :=
    fun a => ⟨fun h => h₀' a h, by
      rintro ⟨r, rfl⟩
      exact isIntegral_algebraMap⟩
  obtain ⟨s, hs⟩ := hrange w ((isIntegral_iff_mem_range_lTensor _ hι₀ w).1 hwint)
  refine ⟨s, hι' ?_⟩
  rw [hcomp, ← ιS.commutes s, hs, hyw, hy, AlgEquiv.apply_symm_apply]

end Stacks

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Sections

variable {X Y : AlgebraicSpaces B S hS}

/-- The projection of the sections of `f_* 𝒪_X` over the chart `e.V` of `Y` to the functions on
the chart `e.U` of `X` named by the chart diagram `e`, as a ring homomorphism.  It is the
canonical map of sections of `AlgebraicGeometry.Space.modulePushforwardCounitApp` for the
structure sheaf, read with the ring structure of the direct-image algebra. -/
def chartDiagramSectionsHom (f : X ⟶ Y) (e : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op e.V) →+*
      (structureSheaf B S hS X.1 X.2).obj.obj (op e.U) :=
  (directImageChartProjectionRingHom B S hS f e.V (indexOfChartDiagram B S hS f e)).hom

/-- The projection of the sections of `f_* 𝒪_X` carries the structure-algebra map to pullback of
functions along the vertical morphism of the chart diagram. -/
theorem chartDiagramSectionsHom_algebraMap (f : X ⟶ Y) (e : ChartDiagram B S hS X.1 Y.1 f.hom)
    (r : (structureSheaf B S hS Y.1 Y.2).obj.obj (op e.V)) :
    chartDiagramSectionsHom f e ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op e.V) r) =
      chartDiagramRestrict B S hS f e r := by
  have h1 : (pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op e.V) r =
      ((structureSharp B S hS f).hom.app (op e.V)).hom r :=
    (congrArg (fun φ : (structureSheaf B S hS Y.1 Y.2).obj.obj (op e.V) →+*
        (pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op e.V) => φ r)
      (pushforwardAlgebra_algebraMap B S hS (Over.mk f) (op e.V))).trans
      (fSharp_app_apply B S hS f (op e.V) r)
  rw [chartDiagramSectionsHom, h1]
  exact (congrArg (fun φ : (structureRingSheaf B S hS Y).obj.obj (op e.V) →+*
      (structureRingSheaf B S hS X).obj.obj
        (indexOfChartDiagram B S hS f e).right => φ r)
    (hom_structureSharp_comp_directImageChartProjectionRingHom B S hS f e.V
      (indexOfChartDiagram B S hS f e))).trans (chartPullback_indexOfChartDiagram B S hS f e r)

/-- The projection of the sections of `f_* 𝒪_X` over `e.V` to a chart `e.U` covering
`X ×_Y e.V` is injective. -/
theorem injective_chartDiagramSectionsHom (f : X ⟶ Y) (e : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hc : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map (chartLift B S hS f e)).hom) :
    Function.Injective (chartDiagramSectionsHom f e) :=
  injective_modulePushforwardCounitApp f (SheafOfModules.unit (structureRingSheaf B S hS X)) e hc

end Sections

section Local

variable {X X' : AlgebraicSpaces B S hS}

/-- **Integral closedness is local on the charts carrying an affine chart diagram.**  Let `A` be
a quasi-coherent algebra sheaf on `X` and `g : X ⟶ X'` a morphism.  If over every chart `W` of
`X` carrying an affine chart diagram over `g` the structure-algebra map of `A` is injective and
every section integral over `𝒪(W)` lies in its image, then `𝒪_X` is integrally closed in `A`.

Such charts are cover-dense (`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`),
so `𝒪_X ⟶ A` is a monomorphism, and on such a chart, which is affine, the sections of the
integral closure of `𝒪_X` in `A` are the integral sections (Stacks 0820); so the integral closure
lies locally, hence globally, in the image of `𝒪_X`. -/
theorem AlgebraSheaf.isIntegrallyClosed_of_hasAffineChartDiagram (g : X ⟶ X')
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherent)
    (hloc : ∀ W : SmallEtale B S hS X.1, HasAffineChartDiagram B S hS g W →
      Function.Injective (A.algebraMap (op W)) ∧
        ∀ x, (A.algebraMap (op W)).IsIntegralElem x → x ∈ Set.range (A.algebraMap (op W))) :
    A.IsIntegrallyClosed := by
  have hcov : ∀ U : SmallEtale B S hS X.1,
      Sieve.generate (fun W (_ : W ⟶ U) => HasAffineChartDiagram B S hS g W) ∈
        SmallEtale.topology B S hS X.1 U := fun U =>
    mem_topology_of_hasAffineChartDiagram B S hS g U _ fun {W} a hW =>
      ⟨W, 𝟙 W, a, hW, Category.id_comp a⟩
  have hmono : Mono A.hom :=
    Stacks.Sites.mono_of_locallyInjective_app _ A.hom fun U =>
      ⟨fun W _ => HasAffineChartDiagram B S hS g W, hcov U, fun V _ hV => (hloc V hV).1⟩
  have hiso : IsIso (pullback.fst (integralClosureInclusion A).right A.hom) :=
    Stacks.Sites.isIso_pullback_fst_of_locally_range_subset _ _ _ fun U =>
      ⟨fun W _ => HasAffineChartDiagram B S hS g W, hcov U, fun V _ hV => by
        rw [range_integralClosureInclusion_app_eq_integralClosure' A hA V hV.1]
        exact fun x hx => (hloc V hV).2 x hx⟩
  intro U
  refine ⟨Stacks.Sites.injective_app_of_mono _ A.hom U, ?_⟩
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact A.integralSections_le_locallyIntegralSections U
      (A.mem_integralSections.2 (AlgebraSheaf.isIntegralElem_apply _ r))
  · intro hx
    rw [← SetLike.mem_coe, ← range_integralClosureInclusion_app] at hx
    obtain ⟨y, rfl⟩ := hx
    let z := (inv (pullback.fst (integralClosureInclusion A).right A.hom)).hom.app U y
    refine ⟨(pullback.snd (integralClosureInclusion A).right A.hom).hom.app U z, ?_⟩
    have h1 : (pullback.fst (integralClosureInclusion A).right A.hom).hom.app U z = y :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m => m.hom)
        (IsIso.inv_hom_id (pullback.fst (integralClosureInclusion A).right A.hom))) U) y
    have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m => m.hom)
      (pullback.condition (f := (integralClosureInclusion A).right) (g := A.hom))) U) z
    show (A.hom.hom.app U)
      ((pullback.snd (integralClosureInclusion A).right A.hom).hom.app U z) = _
    rw [← h1]
    exact h2.symm

end Local

section Main

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- **The chartwise step.**  For a cartesian square with `f` quasi-compact and quasi-separated
and `g` smooth, and `𝒪_Y` integrally closed in `f_* 𝒪_X`, over every diagram `d` of affine
charts over `g` the structure-algebra map of `f'_* 𝒪_{X'}` at `d.U` is injective and every
section integral over `𝒪(d.U)` lies in its image.  See the implementation notes. -/
theorem isIntegrallyClosed_chart_of_isPullback_of_isSmooth (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hg : IsSmooth B S hS g.hom)
    (hcl : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegrallyClosed)
    (d : ChartDiagram B S hS Y'.1 Y.1 g.hom)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V)) :
    Function.Injective ((pushforwardAlgebra B S hS (Over.mk f')).algebraMap (op d.U)) ∧
      ∀ x, ((pushforwardAlgebra B S hS (Over.mk f')).algebraMap (op d.U)).IsIntegralElem x →
        x ∈ Set.range ((pushforwardAlgebra B S hS (Over.mk f')).algebraMap (op d.U)) := by
  obtain ⟨W, b, hb, R, R', t, s, k, hWa, hR'a, hsurj, hpb, hk⟩ :=
    exists_affine_presentation_chartBaseChange f hfqc hfqs d.V hV
  let e : ChartDiagram B S hS X.1 Y.1 f.hom := ⟨W, d.V, b, hb⟩
  let bR : (SmallEtale.toOver B S hS X.1).obj R' ⟶ (SmallEtale.toOver B S hS Y.1).obj d.V :=
    (SmallEtale.toOver B S hS X.1).map (k ≫ t) ≫ b
  have hbR : R'.1.hom ≫ f.hom = yoneda.map bR ≫ d.V.1.hom := chart_comp_comm f (k ≫ t) b hb
  have hts : (SmallEtale.toOver B S hS X.1).map (k ≫ s) ≫ b = bR := by
    simp only [bR, Functor.map_comp, Category.assoc]
    exact congrArg (_ ≫ ·) (chartMap_comp_eq_of_isPullback f e hpb).symm
  let eR : ChartDiagram B S hS X.1 Y.1 f.hom := ⟨R', d.V, bR, hbR⟩
  let T := chartBaseChangeAlong sq d.g d.comm b hb
  let TR := chartBaseChangeAlong sq d.g d.comm bR hbR
  let e' := chartBaseChangeAlongDiagram sq d.g d.comm b hb
  let e'R := chartBaseChangeAlongDiagram sq d.g d.comm bR hbR
  let mt : TR ⟶ T := chartBaseChangeAlongMap sq d.g d.comm bR hbR b hb (k ≫ t) rfl
  let ms : TR ⟶ T := chartBaseChangeAlongMap sq d.g d.comm bR hbR b hb (k ≫ s) hts
  let κ : ChartDiagram B S hS X'.1 X.1 g'.hom :=
    ⟨T, W, pullback.fst b d.g, chartBaseChangeAlong_fst sq d.g d.comm b hb⟩
  let κR : ChartDiagram B S hS X'.1 X.1 g'.hom :=
    ⟨TR, R', pullback.fst bR d.g, chartBaseChangeAlong_fst sq d.g d.comm bR hbR⟩
  have hT : IsAffine (chartScheme T) := isAffine_chartBaseChangeAlong sq d.g d.comm b hb hWa hU hV
  have hTR : IsAffine (chartScheme TR) :=
    isAffine_chartBaseChangeAlong sq d.g d.comm bR hbR hR'a hU hV
  -- the chart rings and their algebra structures
  let A := pushforwardAlgebra B S hS (Over.mk f)
  let A' := pushforwardAlgebra B S hS (Over.mk f')
  let iRS := chartDiagramAlgebra B S hS g d
  have : Algebra.Smooth (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U) :=
    smooth_chartDiagramAlgebra B S hS g hg d hU hV
  let iRC := chartDiagramAlgebra B S hS f e
  let iRD := chartDiagramAlgebra B S hS f eR
  let iRA := chartSectionsAlgebra A d.V
  let iSA := chartSectionsAlgebra A' d.U
  let iSC := chartDiagramAlgebra B S hS f' e'
  let iSD := chartDiagramAlgebra B S hS f' e'R
  -- the two pushouts
  let iCC := chartDiagramAlgebra B S hS g' κ
  let iDD := chartDiagramAlgebra B S hS g' κR
  let iRC' : Algebra (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X'.1 X'.2 κ.U) :=
    ((algebraMap (chartRing B S hS X.1 X.2 W) (chartRing B S hS X'.1 X'.2 κ.U)).comp
      (algebraMap (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 W))).toAlgebra
  let iRD' : Algebra (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X'.1 X'.2 κR.U) :=
    ((algebraMap (chartRing B S hS X.1 X.2 R') (chartRing B S hS X'.1 X'.2 κR.U)).comp
      (algebraMap (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 R'))).toAlgebra
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 W)
      (chartRing B S hS X'.1 X'.2 κ.U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)
      (chartRing B S hS X'.1 X'.2 κ.U) :=
    IsScalarTower.of_algebraMap_eq (fun x => chartDiagramRestrict_chartBaseChangeAlong sq d b hb x)
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 R')
      (chartRing B S hS X'.1 X'.2 κR.U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)
      (chartRing B S hS X'.1 X'.2 κR.U) :=
    IsScalarTower.of_algebraMap_eq
      (fun x => chartDiagramRestrict_chartBaseChangeAlong sq d bR hbR x)
  have : Algebra.IsPushout (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)
      (chartRing B S hS X.1 X.2 W) (chartRing B S hS X'.1 X'.2 κ.U) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W)) :=
      hWa
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y'.1).obj d.U)) := hU
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj d.V)) := hV
    have hpo := isPushout_appTop_of_isPullback (isPullback_chartScheme_chartBaseChangeAlong d.g b)
    exact Algebra.IsPushout.symm (CommRingCat.isPushout_iff_isPushout.1 hpo)
  have : Algebra.IsPushout (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)
      (chartRing B S hS X.1 X.2 R') (chartRing B S hS X'.1 X'.2 κR.U) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj R')) := hR'a
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y'.1).obj d.U)) := hU
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj d.V)) := hV
    have hpo := isPushout_appTop_of_isPullback (isPullback_chartScheme_chartBaseChangeAlong d.g bR)
    exact Algebra.IsPushout.symm (CommRingCat.isPushout_iff_isPushout.1 hpo)
  -- the restriction maps
  let OX := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  let OX' := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)
  have ringX : ∀ (u : R' ⟶ W) (hu : (SmallEtale.toOver B S hS X.1).map u ≫ b = bR) r,
      (OX.obj.map u.op).hom (chartDiagramRestrict B S hS f e r) =
        chartDiagramRestrict B S hS f eR r :=
    fun u hu r => (chartDiagramPullback_comp_apply B S hS ((SmallEtale.toOver B S hS X.1).map u)
      b r).trans (congrArg (fun m => ((forget₂ CommRingCat.{u} RingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op)) r) hu)
  have ringX' : ∀ (u : R' ⟶ W) (hu : (SmallEtale.toOver B S hS X.1).map u ≫ b = bR) r,
      (OX'.obj.map (chartBaseChangeAlongMap sq d.g d.comm bR hbR b hb u hu).op).hom
        (chartDiagramRestrict B S hS f' e' r) = chartDiagramRestrict B S hS f' e'R r :=
    fun u hu r => (chartDiagramPullback_comp_apply B S hS ((SmallEtale.toOver B S hS X'.1).map
      (chartBaseChangeAlongMap sq d.g d.comm bR hbR b hb u hu)) (pullback.snd b d.g) r).trans
      (congrArg (fun m => ((forget₂ CommRingCat.{u} RingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op)) r)
          (chartBaseChangeAlongMap_snd sq d.g d.comm bR hbR b hb u hu))
  let α : chartRing B S hS X.1 X.2 W →ₐ[chartRing B S hS Y.1 Y.2 d.V]
      chartRing B S hS X.1 X.2 R' :=
    { toRingHom := (OX.obj.map (k ≫ t).op).hom, commutes' := ringX _ rfl }
  let β : chartRing B S hS X.1 X.2 W →ₐ[chartRing B S hS Y.1 Y.2 d.V]
      chartRing B S hS X.1 X.2 R' :=
    { toRingHom := (OX.obj.map (k ≫ s).op).hom, commutes' := ringX _ hts }
  let α' : chartRing B S hS X'.1 X'.2 T →ₐ[chartRing B S hS Y'.1 Y'.2 d.U]
      chartRing B S hS X'.1 X'.2 TR :=
    { toRingHom := (OX'.obj.map mt.op).hom, commutes' := ringX' _ rfl }
  let β' : chartRing B S hS X'.1 X'.2 T →ₐ[chartRing B S hS Y'.1 Y'.2 d.U]
      chartRing B S hS X'.1 X'.2 TR :=
    { toRingHom := (OX'.obj.map ms.op).hom, commutes' := ringX' _ hts }
  let eC := Algebra.IsPushout.equiv (chartRing B S hS Y.1 Y.2 d.V)
    (chartRing B S hS Y'.1 Y'.2 d.U) (chartRing B S hS X.1 X.2 W) (chartRing B S hS X'.1 X'.2 κ.U)
  let eD := Algebra.IsPushout.equiv (chartRing B S hS Y.1 Y.2 d.V)
    (chartRing B S hS Y'.1 Y'.2 d.U) (chartRing B S hS X.1 X.2 R')
    (chartRing B S hS X'.1 X'.2 κR.U)
  -- the base change of the restriction maps
  have hfst : ∀ (u : R' ⟶ W) (hu : (SmallEtale.toOver B S hS X.1).map u ≫ b = bR)
      (c : chartRing B S hS X.1 X.2 W) (c' : chartRing B S hS X.1 X.2 R'),
      (OX.obj.map u.op).hom c = c' →
      (OX'.obj.map (chartBaseChangeAlongMap sq d.g d.comm bR hbR b hb u hu).op).hom
        (eC (1 ⊗ₜ c)) = eD (1 ⊗ₜ c') :=
    fun u hu c c' h => by
    simp only [eC, eD, Algebra.IsPushout.equiv_tmul, map_one, one_mul]
    subst h
    exact (chartDiagramPullback_comp_apply B S hS ((SmallEtale.toOver B S hS X'.1).map
      (chartBaseChangeAlongMap sq d.g d.comm bR hbR b hb u hu)) (pullback.fst b d.g) c).trans
      ((congrArg (fun m => ((forget₂ CommRingCat.{u} RingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op)) c)
          (chartBaseChangeAlongMap_fst sq d.g d.comm bR hbR b hb u hu)).trans
      (chartDiagramPullback_comp_apply B S hS (pullback.fst bR d.g)
        ((SmallEtale.toOver B S hS X.1).map u) c).symm)
  -- the sections of the two direct images
  let ι : A.right.obj.obj (op d.V) →ₐ[chartRing B S hS Y.1 Y.2 d.V] chartRing B S hS X.1 X.2 W :=
    { toRingHom := chartDiagramSectionsHom f e
      commutes' := chartDiagramSectionsHom_algebraMap f e }
  let ι' : A'.right.obj.obj (op d.U) →ₐ[chartRing B S hS Y'.1 Y'.2 d.U]
      chartRing B S hS X'.1 X'.2 T :=
    { toRingHom := chartDiagramSectionsHom f' e'
      commutes' := chartDiagramSectionsHom_algebraMap f' e' }
  have hι : Function.Injective ι := injective_chartDiagramSectionsHom f e hsurj
  have hι' : Function.Injective ι' := injective_chartDiagramSectionsHom f' e'
    (isSurjective_chartLift_chartBaseChangeAlongDiagram sq d.g d.comm b hb hsurj)
  have heq : ∀ c, α c = β c → c ∈ Set.range ι := fun c hc =>
    exists_modulePushforwardCounitApp_eq f (SheafOfModules.unit (structureRingSheaf B S hS X)) e
      hsurj t s hpb k hk c
      (((SheafOfModules.unit (structureRingSheaf B S hS X)).val.map_comp_apply t.op k.op
        c).symm.trans (hc.trans ((SheafOfModules.unit
          (structureRingSheaf B S hS X)).val.map_comp_apply s.op k.op c)))
  have hct : ∀ (u : R' ⟶ W) (hu : (SmallEtale.toOver B S hS X.1).map u ≫ b = bR),
      (SmallEtale.toOver B S hS X'.1).map (chartBaseChangeAlongMap sq d.g d.comm bR hbR b hb u hu)
        ≫ e'.g = e'R.g ≫ (SmallEtale.toOver B S hS Y'.1).map (𝟙 d.U) := fun u hu =>
    (chartBaseChangeAlongMap_snd sq d.g d.comm bR hbR b hb u hu).trans
      ((Category.comp_id _).symm.trans
        (congrArg (e'R.g ≫ ·) ((SmallEtale.toOver B S hS Y'.1).map_id d.U).symm))
  have hab : ∀ x, α' (ι' x) = β' (ι' x) := fun x =>
    (modulePushforwardCounitApp_naturality B S hS f'
      (SheafOfModules.unit (structureRingSheaf B S hS X')) e' e'R mt (𝟙 d.U) (hct _ rfl)
        x).symm.trans
      (modulePushforwardCounitApp_naturality B S hS f'
        (SheafOfModules.unit (structureRingSheaf B S hS X')) e' e'R ms (𝟙 d.U) (hct _ hts) x)
  have h₀ : Function.Injective (algebraMap (chartRing B S hS Y.1 Y.2 d.V)
      (A.right.obj.obj (op d.V))) := (hcl (op d.V)).1
  have h₀' : ∀ a : A.right.obj.obj (op d.V), _root_.IsIntegral (chartRing B S hS Y.1 Y.2 d.V) a →
      a ∈ Set.range (algebraMap (chartRing B S hS Y.1 Y.2 d.V) (A.right.obj.obj (op d.V))) := by
    intro a ha
    have hmem : a ∈ A.locallyIntegralSections (op d.V) :=
      A.integralSections_le_locallyIntegralSections (op d.V) (A.mem_integralSections.2 ha)
    rwa [← (hcl (op d.V)).2] at hmem
  exact Stacks.injective_and_isIntegral_mem_range_of_tensor_equalizer α β ι hι heq h₀ h₀' eC eD
    α' β' (fun c => hfst _ rfl c _ rfl) (fun c => hfst _ hts c _ rfl) ι' hι' hab

/-- **Integral closedness of `𝒪` in the direct image of `𝒪` is preserved by smooth base
change.**  For a cartesian square of algebraic spaces with `f : X ⟶ Y` quasi-compact and
quasi-separated and `g : Y' ⟶ Y` smooth, if `𝒪_Y` is integrally closed in `f_* 𝒪_X` then
`𝒪_{Y'}` is integrally closed in `f'_* 𝒪_{X'}`. -/
theorem isIntegrallyClosed_pushforwardAlgebra_of_isPullback_of_isSmooth
    (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hg : IsSmooth B S hS g.hom)
    (hcl : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegrallyClosed) :
    (pushforwardAlgebra B S hS (Over.mk f')).IsIntegrallyClosed := by
  have hsq : IsPullback g'.hom f'.hom f.hom g.hom := sq.map (ObjectProperty.ι _)
  have hqc : IsQuasiCompact B S hS f'.hom := isQuasiCompact_of_isPullback B S hS hsq hfqc
  have hqs : IsQuasiSeparated B S hS f'.hom := isQuasiSeparated_of_isPullback B S hS hsq hfqs
  refine AlgebraSheaf.isIntegrallyClosed_of_hasAffineChartDiagram g _
    (isQuasicoherent_pushforwardAlgebra B S hS f' hqc hqs fun hqc hqs F hF =>
      isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f' hqc hqs F hF) ?_
  rintro W ⟨hWa, V, q, hcomm, hVa⟩
  exact isIntegrallyClosed_chart_of_isPullback_of_isSmooth sq hfqc hfqs hg hcl
    ⟨W, V, q, hcomm.symm⟩ hWa hVa

end Main

end AlgebraicGeometry.Space

end
