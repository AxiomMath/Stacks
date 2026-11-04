module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueingTower

/-!
# Stacks 0AGK from the structure maps `𝒪_X ⟶ 𝒜_n`

In the situation of Stacks 0AGH, let `X_n` be coequalizers of the kernel pairs of
`Y_n = X' ⨿ Z_n ⟶ X` and `𝒜_n = (X_n ⟶ X)_* 𝒪`. This file states the geometric half of Stacks
0AGK in terms of the structure maps `𝒪_X ⟶ 𝒜_n` themselves, rather than through `(𝟙_X)_* 𝒪_X`, and
proves that `𝒪_X ⟶ 𝒜_n` is injective once `Ker(𝒪_X ⟶ f_* 𝒪_{X'}) ∩ 𝓘ⁿ` vanishes.

## Main results

* `structureSharp_app_eq_zero_iff`: a section lies in the kernel of `𝒪_X ⟶ Y_* 𝒪_Y` exactly when
  the structure map of the direct-image algebra `Y_* 𝒪` kills it.
* `exists_section_of_algebraMap_range_le`: the factorization through a closed-immersion section,
  from injectivity of `𝒪_X ⟶ Q_* 𝒪` and containment of the image of `t♯` in its image.
* `CoequalizerGlueSituation.ClosedSubspaceSystem.injective_algebraMap_stage`: `𝒪_X ⟶ 𝒜_n` is
  injective as soon as `Ker(𝒪_X ⟶ f_* 𝒪_{X'}) ∩ Ker(𝒪_X ⟶ 𝒪_{Z_n}) = 0`.
* `CoequalizerGlueSituation.exists_factorsThroughSection_of_eventually`: Stacks 0AGK for the tower
  of infinitesimal neighbourhoods, from the conclusion of Stacks 0AGG, the eventual vanishing of
  `Ker(𝒪_X ⟶ f_* 𝒪_{X'}) ∩ 𝓘ⁿ`, and the eventual containment of the image of `𝒜_{n+m} ⟶ 𝒜_n` in
  that of `𝒪_X`.

## Implementation notes

The two remaining hypotheses of `exists_factorsThroughSection_of_eventually` are the two middle
paragraphs of the proof of Stacks 0AGK. The vanishing of `Ker(𝒪_X ⟶ f_* 𝒪_{X'}) ∩ 𝓘ⁿ` for
`n ≫ 0` is Stacks 07UK (the kernel is supported on `|Z|`, since `f` is an isomorphism over `U`)
followed by Artin-Rees, Stacks 07UL. The containment of images uses Stacks 08AY, clause (1), at
`p = 0` for `f : X' ⟶ X` over affine étale charts, finiteness of `Γ(X', 𝒪_{X'})` over the chart
(Stacks 08AR), and the description of `𝒜_n` inside `f_* 𝒪_{X'} × 𝒪_X/𝓘ⁿ`.

## References

* [Stacks Project, Tag 0AGK](https://stacks.math.columbia.edu/tag/0AGK)
* [Stacks Project, Tag 0AGJ](https://stacks.math.columbia.edu/tag/0AGJ)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Kernel ideal sheaves and structure maps of direct-image algebras -/

/-- The `RingCat`-valued structure map and the `CommRingCat`-valued one agree on sections. -/
theorem structureSharp_app_eq_structureSharpCommRing_app {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) (r : (structureSheaf B S hS Y.1 Y.2).obj.obj U) :
    (structureSharp B S hS f).hom.app U r = (structureSharpCommRing B S hS f).hom.app U r := by
  rw [← map_structureSharpCommRing B S hS f]
  rfl

/-- A section of `𝒪_X` lies in the kernel of the structure map `𝒪_X ⟶ Y_* 𝒪_Y` (whose kernels
form the kernel ideal sheaf, `AlgebraicGeometry.Space.kernelIdealSheaf_obj`) exactly when the
structure map of the direct-image algebra `Y_* 𝒪` kills it. -/
theorem structureSharp_app_eq_zero_iff {X : AlgebraicSpaces B S hS} (Y : Over X)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (r : (structureSheaf B S hS X.1 X.2).obj.obj U) :
    (structureSharp B S hS Y.hom).hom.app U r = 0 ↔
      (pushforwardAlgebra B S hS Y).algebraMap U r = 0 := by
  rw [structureSharp_app_eq_structureSharpCommRing_app]
  rfl

/-! ### The section criterion through the structure maps -/

/-- The structure map `𝒪_X ⟶ (𝟙_X)_* 𝒪_X` is bijective on every étale chart (the identity clause
of Stacks 03G8). -/
theorem bijective_algebraMap_pushforwardAlgebra_id (X : AlgebraicSpaces B S hS)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Bijective ((pushforwardAlgebra B S hS (Over.mk (𝟙 X))).algebraMap U) := by
  have := isIso_fSharp_id B S hS X
  have : IsIso ((smallEtaleRingedToposHom B S hS (𝟙 X)).fSharp.hom.app U) := inferInstance
  exact ConcreteCategory.bijective_of_isIso
    ((smallEtaleRingedToposHom B S hS (𝟙 X)).fSharp.hom.app U)

variable {X : AlgebraicSpaces B S hS} {P Q : Over X} (t : Q ⟶ P)

/-- The structure map `𝒪_X ⟶ Q_* 𝒪` is the composite of `𝒪_X ⟶ (𝟙_X)_* 𝒪_X` with the ring map
`(𝟙_X)_* 𝒪_X ⟶ Q_* 𝒪` induced by `Q ⟶ 𝟙_X` over `X`. -/
theorem pushforwardRingMap_toIdOver_algebraMap (V : SmallEtale B S hS X.1)
    (r : (structureSheaf B S hS X.1 X.2).obj.obj (op V)) :
    (pushforwardRingMap B S hS (toIdOver B S hS Q)).hom.app (op V)
        ((pushforwardAlgebra B S hS (Over.mk (𝟙 X))).algebraMap (op V) r) =
      (pushforwardAlgebra B S hS Q).algebraMap (op V) r :=
  (pushforwardAlgebraMap B S hS (toIdOver B S hS Q)).comm (op V) r

/-- **The section criterion, through the structure maps.** For `P` finite and `Q` affine over
`X` and `t : Q ⟶ P` over `X`: if the structure map `𝒪_X ⟶ Q_* 𝒪` is injective and its image
contains that of `t♯ : P_* 𝒪 ⟶ Q_* 𝒪`, then `t` factors as `Q ⟶ X ⟶ P` through a section
`X ⟶ P` of `P ⟶ X`, which is a closed immersion. -/
theorem exists_section_of_algebraMap_range_le (hP : IsFinite B S hS P.hom.hom)
    (hinj : ∀ V : SmallEtale B S hS X.1,
      Function.Injective ((pushforwardAlgebra B S hS Q).algebraMap (op V)))
    (hrange : ∀ (V : SmallEtale B S hS X.1)
      (b : (pushforwardAlgebra B S hS P).right.obj.obj (op V)),
      ∃ r : (structureSheaf B S hS X.1 X.2).obj.obj (op V),
        (pushforwardAlgebra B S hS Q).algebraMap (op V) r =
          (pushforwardRingMap B S hS t).hom.app (op V) b) :
    ∃ c : X ⟶ P.left, IsClosedImmersion B S hS c.hom ∧ c ≫ P.hom = 𝟙 X ∧
      Q.hom ≫ c = t.left := by
  refine exists_section_of_range_le t (fun V x y hxy => ?_) (fun V b => ?_) hP
  · obtain ⟨x₀, rfl⟩ := (bijective_algebraMap_pushforwardAlgebra_id X (op V)).2 x
    obtain ⟨y₀, rfl⟩ := (bijective_algebraMap_pushforwardAlgebra_id X (op V)).2 y
    rw [pushforwardRingMap_toIdOver_algebraMap, pushforwardRingMap_toIdOver_algebraMap] at hxy
    rw [hinj V hxy]
  · obtain ⟨r, hr⟩ := hrange V b
    exact ⟨_, (pushforwardRingMap_toIdOver_algebraMap V r).trans hr⟩

namespace CoequalizerGlueSituation

/-- `X'` as an algebraic space over `X`, through the proper modification `f`. -/
abbrev modificationOver (T : CoequalizerGlueSituation.{u}) : Over T.targetSpace :=
  Over.mk (ObjectProperty.homMk T.f : T.modificationSpace ⟶ T.targetSpace)

namespace ClosedSubspaceSystem

variable {T : CoequalizerGlueSituation.{u}} (N : T.ClosedSubspaceSystem)
  (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (N.glueMapAt n))

/-- `Z_n` as an algebraic space over `X`. -/
abbrev memberOver (n : ℕ) : Over T.targetSpace := Over.mk (N.toTarget n)

/-- The morphism `X' ⟶ Y_n ⟶ X_n`, over `X`. -/
abbrev modificationToStage (n : ℕ) : T.modificationOver ⟶ N.stageOver D n :=
  Over.homMk (coprod.inl ≫ (D n).π) (by
    change (coprod.inl ≫ (D n).π) ≫ (D n).toTarget = _
    rw [Category.assoc, (D n).fac, glueMapAt, coprod.inl_desc]
    rfl)

/-- The morphism `Z_n ⟶ Y_n ⟶ X_n`, over `X`. -/
abbrev memberToStage (n : ℕ) : N.memberOver n ⟶ N.stageOver D n :=
  Over.homMk (coprod.inr ≫ (D n).π) (by
    change (coprod.inr ≫ (D n).π) ≫ (D n).toTarget = _
    rw [Category.assoc, (D n).fac, glueMapAt, coprod.inr_desc]
    rfl)

/-- A section of `𝒪_X` killed by `𝒪_X ⟶ 𝒜_n` is killed by `𝒪_X ⟶ f_* 𝒪_{X'}` and by
`𝒪_X ⟶ 𝒪_{Z_n}`: both factor through `𝒜_n`. -/
theorem structureSharp_app_eq_zero_of_algebraMap_eq_zero (n : ℕ)
    (V : SmallEtale T.B T.S T.hS T.X)
    (r : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op V))
    (hr : (pushforwardAlgebra T.B T.S T.hS (N.stageOver D n)).algebraMap (op V) r = 0) :
    (structureSharp T.B T.S T.hS (ObjectProperty.homMk T.f :
        T.modificationSpace ⟶ T.targetSpace)).hom.app (op V) r = 0 ∧
      (structureSharp T.B T.S T.hS (N.toTarget n)).hom.app (op V) r = 0 :=
  ⟨(structureSharp_app_eq_zero_iff T.modificationOver (op V) r).2 (by
      rw [← (pushforwardAlgebraMap T.B T.S T.hS (N.modificationToStage D n)).comm (op V) r, hr,
        map_zero]),
    (structureSharp_app_eq_zero_iff (N.memberOver n) (op V) r).2 (by
      rw [← (pushforwardAlgebraMap T.B T.S T.hS (N.memberToStage D n)).comm (op V) r, hr,
        map_zero])⟩

/-- **`𝒪_X ⟶ 𝒜_n` is injective once `Ker(𝒪_X ⟶ f_* 𝒪_{X'}) ∩ Ker(𝒪_X ⟶ 𝒪_{Z_n}) = 0`.** -/
theorem injective_algebraMap_stage (n : ℕ)
    (hbot : kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.f :
        T.modificationSpace ⟶ T.targetSpace) ⊓ kernelIdealSheaf T.B T.S T.hS (N.toTarget n) = ⊥)
    (V : SmallEtale T.B T.S T.hS T.X) :
    Function.Injective
      ((pushforwardAlgebra T.B T.S T.hS (N.stageOver D n)).algebraMap (op V)) := by
  refine (injective_iff_map_eq_zero _).2 fun r hr => ?_
  obtain ⟨h1, h2⟩ := N.structureSharp_app_eq_zero_of_algebraMap_eq_zero D n V r hr
  let r' : (SheafOfModules.unit (structureRingSheaf T.B T.S T.hS T.targetSpace)).val.obj (op V) :=
    r
  have hmem : r' ∈ (kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.f :
      T.modificationSpace ⟶ T.targetSpace) ⊓
        kernelIdealSheaf T.B T.S T.hS (N.toTarget n)).obj (op V) := ⟨h1, h2⟩
  rwa [hbot, SheafOfModules.Submodule.bot_obj, Submodule.mem_bot] at hmem

/-- The transition `𝒜_{n+m} ⟶ 𝒜_n` has image in that of `𝒪_X` over every étale chart. -/
def RangeLeStructureAt (n m : ℕ) : Prop :=
  ∀ (V : SmallEtale T.B T.S T.hS T.X)
    (b : (pushforwardAlgebra T.B T.S T.hS (N.stageOver D (n + m))).right.obj.obj (op V)),
    ∃ r : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op V),
      (pushforwardAlgebra T.B T.S T.hS (N.stageOver D n)).algebraMap (op V) r =
        (pushforwardRingMap T.B T.S T.hS (N.towerTransitionOver D n m)).hom.app (op V) b

end ClosedSubspaceSystem

variable (T : CoequalizerGlueSituation.{u})

/-- **Stacks 0AGK, from its two algebraic steps.** For any choice of coequalizers `X_n` of the
kernel pairs of `X' ⨿ Z_n ⟶ X` along the infinitesimal neighbourhoods `Z_n` of `Z`: if
`Ker(𝒪_X ⟶ f_* 𝒪_{X'}) ∩ 𝓘ⁿ` vanishes for `n ≫ 0` and, for `n ≫ 0`, some `𝒜_{n+m} ⟶ 𝒜_n` has
image in that of `𝒪_X`, then for all `n` large enough there is an `m` such that
`X_n ⟶ X_{n+m}` factors through a closed immersion `X ⟶ X_{n+m}`, a section of `X_{n+m} ⟶ X`.
Stacks 0AGG enters as `hAGG`, through finiteness of `X_{n+m} ⟶ X`. -/
theorem exists_factorsThroughSection_of_eventually
    (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS)
    (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (T.neighbourhoodSystem.glueMapAt n))
    (hK : ∃ n₀, ∀ n, n₀ ≤ n → kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.f :
        T.modificationSpace ⟶ T.targetSpace) ⊓ T.neighbourhoodIdeal n = ⊥)
    (hrange : ∃ n₁, ∀ n, n₁ ≤ n → ∃ m, T.neighbourhoodSystem.RangeLeStructureAt D n m) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∃ m, T.neighbourhoodSystem.FactorsThroughSection D n m := by
  obtain ⟨n₀, hn₀⟩ := hK
  obtain ⟨n₁, hn₁⟩ := hrange
  refine ⟨max n₀ n₁, fun n hn => ?_⟩
  obtain ⟨m, hm⟩ := hn₁ n (le_of_max_le_right hn)
  have hbot := hn₀ n (le_of_max_le_left hn)
  rw [← T.kernelIdealSheaf_neighbourhoodSystem_toTarget n] at hbot
  refine ⟨m, ?_⟩
  obtain ⟨c, hc, hsec, hfac⟩ := exists_section_of_algebraMap_range_le
    (T.neighbourhoodSystem.towerTransitionOver D n m)
    (hAGG.isFinite_toTarget _ T.locallyNoetherian
      (T.neighbourhoodSystem.isProper_glueMapAt (n + m)) (D (n + m)))
    (T.neighbourhoodSystem.injective_algebraMap_stage D n hbot) hm
  exact ⟨c, hc, hsec, hfac⟩

end CoequalizerGlueSituation

end AlgebraicGeometry.Space

end
