module

public import StacksFrontier.Deformation.Formal.MinimalVersal.ArtinianFormalization

/-!
# The tower of subalgebras cut out by the minimal stages

The minimal stages of a formal object cut out a tower of Artinian local subalgebras of the bases
of its levels, with surjective transition maps and with the `(n + 1)`-st power of the maximal
ideal vanishing at stage `n`. This file constructs that tower, its inclusions into the bases of
the levels, and the composite transition maps along it.

## Main definitions

* `Deformation.stageBaseTower`: the tower of Artinian local algebras cut out by the minimal stages
  of a formal object.
* `Deformation.stageBaseTowerTransition`: the transition maps of the tower `stageBaseTower`.
* `Deformation.stageBaseTowerInclusion`: the inclusion of the `n`-th term of `stageBaseTower` into
  the base of the `n`-th level.
* `Deformation.stageTowerPath`: the composite transition map of `stageBaseTower` from level `m`
  down to level `n ≤ m`.
* `Deformation.formalObjectPath`: the composite transition morphism of a formal object from level
  `m` down to level `n ≤ m`.

## Main results

* `Deformation.stageBaseTransition_surjective`: the transition maps between the bases of the
  minimal stages are surjective.
* `Deformation.stageBaseTransition_fac`: the transition maps between the bases of the minimal
  stages commute with their inclusions into the levels of the formal object.
* `Deformation.stageBaseTowerInclusion_injective`: the inclusions of `stageBaseTower` into the
  bases of the levels are injective.
* `Deformation.stageBaseTower_maximalIdeal_pow_eq_bot`: the `(n + 1)`-st power of the maximal
  ideal of the `n`-th term of `stageBaseTower` vanishes.
* `Deformation.stageBaseTowerInclusion_fac`: the inclusions of `stageBaseTower` commute with the
  transition maps on both sides.
* `Deformation.stageBaseTowerInclusion_path`: the inclusions of `stageBaseTower` commute with the
  composite transition maps.
* `Deformation.stageTowerPath_coordinate`: a compatible sequence in the inverse limit of
  `stageBaseTower` is carried by the composite transition maps to its earlier coordinates.
* `Deformation.artinianAdicQuotient_isIso_at_stage`: the projection of the `n`-th term of
  `stageBaseTower` onto its own `n`-th adic truncation is an isomorphism, since its maximal ideal
  already has vanishing `(n + 1)`-st power.
* `Deformation.artinianFormalizationInclusion_isIso_at_stage`: the arrow from the `n`-th minimal
  stage into the `n`-th level of its own formalization is an isomorphism.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}


section
variable [IsNoetherianRing Λ] [Module.Finite Λ k]
/-- The transition maps between the bases of the minimal stages are surjective. -/
theorem stageBaseTransition_surjective
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    Function.Surjective (stageBaseTransition hp hS1 ξ n).hom := by
  classical
  let D := descentPushforward p hp (ξ.transition n)
  let X := minimalStages hp hS1 ξ (n + 1)
  let e := stageComparisonIso hp hS1 ξ n
  have hinc := descentPushforward_inclusion_surjective (ξ.transition n) D X
  have : IsIso e.hom := Iso.isIso_hom e
  have : IsIso e.hom.hom := by infer_instance
  have hleft : IsIso ((Over.forget (ξ.level n)).map e.hom.hom) := Functor.map_isIso _ _
  have he : IsIso (e.hom.hom.left) := by simpa using hleft
  have hmap : IsIso (p.map e.hom.hom.left) := by infer_instance
  have heSurj := artinianHom_surjective_of_isIso (p.map e.hom.hom.left)
  intro b
  obtain ⟨c, hc⟩ := heSurj b
  obtain ⟨a, ha⟩ := hinc c
  refine ⟨a, ?_⟩
  change (p.map (D.inclusion X ≫ e.hom.hom.left)).hom a = b
  rw [Functor.map_comp, ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply, ha, hc]

/-- The transition maps between the bases of the minimal stages commute with their inclusions into
the levels of the formal object. -/
theorem stageBaseTransition_fac
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    stageBaseTransition hp hS1 ξ n ≫ p.map (minimalStages hp hS1 ξ n).obj.hom =
      p.map (minimalStages hp hS1 ξ (n + 1)).obj.hom ≫ p.map (ξ.transition n) := by
  let D := descentPushforward p hp (ξ.transition n)
  let X := minimalStages hp hS1 ξ (n + 1)
  let e := stageComparisonIso hp hS1 ξ n
  have hefac : e.hom.hom.left ≫ (minimalStages hp hS1 ξ n).obj.hom =
      (D.functor.obj X).obj.hom := Over.w e.hom.hom
  change p.map (D.inclusion X ≫ e.hom.hom.left) ≫ p.map (minimalStages hp hS1 ξ n).obj.hom =
    p.map X.obj.hom ≫ p.map (ξ.transition n)
  rw [← Functor.map_comp, Category.assoc, hefac, D.inclusion_fac, Functor.map_comp]

/-- The tower of Artinian local algebras cut out by the minimal stages of a formal object. -/
noncomputable def stageBaseTower
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k :=
  fun n => p.obj (minimalStages hp hS1 ξ n).obj.left

/-- The transition maps of the tower `stageBaseTower`. -/
noncomputable def stageBaseTowerTransition
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    stageBaseTower hp hS1 ξ (n + 1) ⟶ stageBaseTower hp hS1 ξ n :=
  stageBaseTransition hp hS1 ξ n

/-- The inclusion of the `n`-th term of `stageBaseTower` into the base of the `n`-th level. -/
noncomputable def stageBaseTowerInclusion
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    stageBaseTower hp hS1 ξ n ⟶ p.obj (ξ.level n) :=
  p.map (minimalStages hp hS1 ξ n).obj.hom

/-- The inclusions of `stageBaseTower` into the bases of the levels are injective. -/
theorem stageBaseTowerInclusion_injective
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    Function.Injective (stageBaseTowerInclusion hp hS1 ξ n).hom :=
  (minimalStages hp hS1 ξ n).property

/-- The `(n + 1)`-st power of the maximal ideal of the `n`-th term of `stageBaseTower` vanishes. -/
theorem stageBaseTower_maximalIdeal_pow_eq_bot
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    maximalIdeal (stageBaseTower hp hS1 ξ n) ^ (n + 1) = ⊥ := by
  let i := stageBaseTowerInclusion hp hS1 ξ n
  have hB : maximalIdeal (p.obj (ξ.level n)) ^ (n + 1) = ⊥ := by
    rw [ξ.level_eq n]
    change maximalIdeal (AdicTruncation.obj ξ.base n) ^ (n + 1) = ⊥
    let q : ξ.base →+* AdicTruncation.obj ξ.base n :=
      Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n)
    rw [← IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective,
      ← Ideal.map_pow]
    exact Ideal.map_quotient_self (AdicTruncation.ideal ξ.base n)
  have hpow : Ideal.map i.hom.toRingHom (maximalIdeal _ ^ (n + 1)) = ⊥ := by
    rw [Ideal.map_pow]
    exact le_bot_iff.mp ((Ideal.pow_right_mono
      (IsLocalRing.map_maximalIdeal_le i.hom.toRingHom) (n + 1)).trans_eq hB)
  refine le_antisymm (fun x hx => Ideal.mem_bot.mpr ?_) bot_le
  apply stageBaseTowerInclusion_injective hp hS1 ξ n
  simpa using RingHom.mem_ker.mp ((Ideal.map_eq_bot_iff_le_ker _).mp hpow hx)

/-- The inclusions of `stageBaseTower` commute with the transition maps on both sides. -/
theorem stageBaseTowerInclusion_fac
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    stageBaseTowerTransition hp hS1 ξ n ≫
        stageBaseTowerInclusion hp hS1 ξ n =
      stageBaseTowerInclusion hp hS1 ξ (n + 1) ≫ p.map (ξ.transition n) :=
  stageBaseTransition_fac hp hS1 ξ n

/-- The composite transition map of `stageBaseTower` from level `m` down to level `n ≤ m`. -/
noncomputable def stageTowerPath
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n m : ℕ) (h : n ≤ m) :
    stageBaseTower hp hS1 ξ m ⟶ stageBaseTower hp hS1 ξ n :=
  Nat.leRecOn h (fun {j} f => stageBaseTowerTransition hp hS1 ξ j ≫ f)
    (𝟙 (stageBaseTower hp hS1 ξ n))


/-- The composite transition morphism of a formal object from level `m` down to level `n ≤ m`. -/
noncomputable def formalObjectPath
    (ξ : FormalObject p) (n m : ℕ) (h : n ≤ m) : ξ.level m ⟶ ξ.level n :=
  Nat.leRecOn h (fun {j} f => ξ.transition j ≫ f) (𝟙 (ξ.level n))

/-- The inclusions of `stageBaseTower` commute with the composite transition maps. -/
theorem stageBaseTowerInclusion_path
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n m : ℕ) (h : n ≤ m) :
    stageTowerPath hp hS1 ξ n m h ≫ stageBaseTowerInclusion hp hS1 ξ n =
      stageBaseTowerInclusion hp hS1 ξ m ≫ p.map (formalObjectPath ξ n m h) := by
  induction m, h using Nat.le_induction with
  | base =>
      simp only [stageTowerPath, formalObjectPath, Nat.leRecOn_self,
        Category.id_comp, p.map_id, Category.comp_id]
  | succ m hm ih =>
      rw [stageTowerPath, Nat.leRecOn_succ hm, formalObjectPath,
        Nat.leRecOn_succ hm]
      calc
        (stageBaseTowerTransition hp hS1 ξ m ≫
            stageTowerPath hp hS1 ξ n m hm) ≫ stageBaseTowerInclusion hp hS1 ξ n =
          (stageBaseTowerTransition hp hS1 ξ m ≫
            stageBaseTowerInclusion hp hS1 ξ m) ≫
            p.map (formalObjectPath ξ n m hm) := by
              rw [Category.assoc, ih, ← Category.assoc]
        _ = (stageBaseTowerInclusion hp hS1 ξ (m + 1) ≫
            p.map (ξ.transition m)) ≫ p.map (formalObjectPath ξ n m hm) := by
              rw [stageBaseTowerInclusion_fac]
        _ = stageBaseTowerInclusion hp hS1 ξ (m + 1) ≫
            p.map (ξ.transition m ≫ formalObjectPath ξ n m hm) := by
              rw [Functor.map_comp, Category.assoc]

/-- A compatible sequence in the inverse limit of `stageBaseTower` is carried by the composite
transition maps to its earlier coordinates. -/
theorem stageTowerPath_coordinate
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (z : inverseLimit (stageBaseTower hp hS1 ξ)
      (stageBaseTowerTransition hp hS1 ξ))
    (n m : ℕ) (h : n ≤ m) :
    (stageTowerPath hp hS1 ξ n m h).hom (z.1 m) = z.1 n := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [stageTowerPath, Nat.leRecOn_self]
      rfl
  | succ m hm ih =>
      rw [stageTowerPath, Nat.leRecOn_succ, ArtinianLocalAlgCat.comp_hom,
        AlgHom.comp_apply, z.2 m]
      exact ih

/-- The projection of the `n`-th term of `stageBaseTower` onto its own `n`-th adic truncation is an
isomorphism, since its maximal ideal already has vanishing `(n + 1)`-st power. -/
theorem artinianAdicQuotient_isIso_at_stage
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    IsIso (artinianAdicQuotient (stageBaseTower hp hS1 ξ n) n) := by
  have hpow := stageBaseTower_maximalIdeal_pow_eq_bot hp hS1 ξ n
  have hbij : Function.Bijective (artinianAdicQuotient (stageBaseTower hp hS1 ξ n) n).hom := by
    change Function.Bijective
      (Ideal.Quotient.mk (AdicTruncation.ideal
        (artinianToComplete.obj (stageBaseTower hp hS1 ξ n)) n))
    rw [Ideal.Quotient.mk_bijective_iff_eq_bot]
    change maximalIdeal (stageBaseTower hp hS1 ξ n) ^ (n + 1) = ⊥
    exact hpow
  exact ArtinianLocalAlgCat.isIso_of_bijective_hom _ hbij

/-- The arrow from the `n`-th minimal stage into the `n`-th level of its own formalization is an
isomorphism. -/
theorem artinianFormalizationInclusion_isIso_at_stage
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    IsIso (artinianFormalizationInclusion hp
      (minimalStages hp hS1 ξ n).obj.left n) := by
  have hq := artinianAdicQuotient_isIso_at_stage hp hS1 ξ n
  let : IsIso (artinianAdicQuotient
      (p.obj (minimalStages hp hS1 ξ n).obj.left) n) := hq
  have hlift := artinianFormalizationInclusion_lift hp
    (minimalStages hp hS1 ξ n).obj.left n
  let := hlift
  have hobj : p.obj (artinianFormalizationLevel hp
      (minimalStages hp hS1 ξ n).obj.left n) =
      AdicTruncation.obj (artinianToComplete.obj
        (p.obj (minimalStages hp hS1 ξ n).obj.left)) n := by
    change p.obj (cofiberedPushforwardObj hp
      (artinianAdicQuotient (p.obj (minimalStages hp hS1 ξ n).obj.left) n)
      (minimalStages hp hS1 ξ n).obj.left rfl) = _
    exact cofiberedPushforwardObj_eq hp
      (artinianAdicQuotient (p.obj (minimalStages hp hS1 ξ n).obj.left) n)
      (minimalStages hp hS1 ξ n).obj.left rfl
  have hfac : artinianAdicQuotient
      (p.obj (minimalStages hp hS1 ξ n).obj.left) n =
      p.map (artinianFormalizationInclusion hp
        (minimalStages hp hS1 ξ n).obj.left n) ≫ eqToHom hobj := by
    simpa using IsHomLift.fac p
      (artinianAdicQuotient (p.obj (minimalStages hp hS1 ξ n).obj.left) n)
      (artinianFormalizationInclusion hp (minimalStages hp hS1 ξ n).obj.left n)
  let g := p.map (artinianFormalizationInclusion hp
    (minimalStages hp hS1 ξ n).obj.left n)
  let q := artinianAdicQuotient (p.obj (minimalStages hp hS1 ξ n).obj.left) n
  let e := eqToHom hobj
  have hfac' : q = g ≫ e := by simpa [g, q, e] using hfac
  have hmap : IsIso g := by
    let : IsIso e := ⟨eqToHom hobj.symm, by simp [e], by simp [e]⟩
    exact IsIso.of_isIso_fac_right hfac'.symm
  exact isIso_of_isIso_map hp _

end

end Deformation

end
