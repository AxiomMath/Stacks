module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueingTowerInjective

/-!
# The image of `𝒜_{n+m} ⟶ 𝒜_n` lies in `𝒪_X`, from an adic bound for `f : X' ⟶ X`

In the situation of Stacks 0AGH, given an adic bound for `f : X' ⟶ X`, the image of
`𝒜_{n+m} ⟶ 𝒜_n` lies in that of `𝒪_X` for all `n` large enough and some `m`; this is the last
paragraph of the proof of Stacks 0AGK. Write `X'_k = X' ×_X Z_k` and let
`ρ_k : f_* 𝒪_{X'} ⟶ (X'_k ⟶ X)_* 𝒪` be restriction. The input is
`AlgebraicGeometry.Space.CoequalizerGlueSituation.AdicKernelBound`: there is a `c` such that for
`k ≥ c` every section of `Ker ρ_k` is, locally on `X`, the image of a section of `𝓘ᵏ⁺¹⁻ᶜ` under
`f♯ : 𝒪_X ⟶ f_* 𝒪_{X'}` (the infinitesimal neighbourhood of stage `k` being `Z_{k+1}`, cut out by
`𝓘ᵏ⁺¹`). On an affine étale chart `V = Spec R` of `X` with `B = Γ(X'_V, 𝒪)` this is
`Ker(B ⟶ Γ(X'_V, 𝒪/𝓘ᵏ⁺¹𝒪)) ⊆ 𝓘ᵏ⁺¹⁻ᶜ · im(R ⟶ B)`. The source obtains it from Stacks 08AY,
clause (1), at `p = 0` (`Ker ⊆ I^{k+1-c₁} B`) and from finiteness of `B` over `R` (Stacks 08AR)
together with `R ⟶ B` being an isomorphism after inverting any element of `I`
(`I^{t} B ⊆ im R`), with `c = c₁ + t`.

## The argument

Let `b` be a section of `𝒜_k`, `k = n + m`, with restrictions `a ∈ f_* 𝒪_{X'}` and
`z ∈ 𝒪_{Z_{k+1}}`. Locally `z = i♯ t` (Stacks 03MB, `i♯` is locally surjective). The two
restrictions of `b` to `X'_k` agree, because `X'_k ⟶ X' ⨿ Z_{k+1}` through either summand lands in
the kernel pair which the quotient map coequalizes; so `a - f♯ t` lies in `Ker ρ_k`, and locally
`a - f♯ t = f♯ s` with `s ∈ 𝓘ᵏ⁺¹⁻ᶜ ⊆ 𝓘ⁿ⁺¹` once `m ≥ c`. Then `r = t + s` has
`𝒪_X ⟶ 𝒜_n` value with the same two restrictions as the image of `b` in `𝒜_n`, so they agree
(`eq_zero_of_restrictions_eq_zero`); the local `r` are compatible since `𝒪_X ⟶ 𝒜_n` is injective
for `n ≫ 0`, and glue.

## Main results

* `AlgebraicGeometry.Space.exists_eq_of_locally_mem_range`: gluing through an injective morphism
  of sheaves of rings.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.ClosedSubspaceSystem.crossToModification_comp`:
  the equalizer condition on `X' ×_X Z_k`.
* `CoequalizerGlueSituation.ClosedSubspaceSystem.modificationToStage_comp_towerTransitionOver`
  and `memberToStage_comp_towerTransitionOver`: the restrictions of `𝒜_{n+m} ⟶ 𝒜_n`.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.AdicKernelBound`: the adic bound for `f`,
  the input from Stacks 08AY and Stacks 08AR.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.restrict_cross_eq`: the equalizer condition on
  sections.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.rangeLeStructureAt_of_kernelBound`: the local
  step and the gluing, for one `n`.
* `CoequalizerGlueSituation.eventually_rangeLeStructureAt_of_adicKernelBound` and
  `CoequalizerGlueSituation.exists_factorsThroughSection_of_adicKernelBound`: for `X`
  quasi-compact, the eventual bound on the image of `𝒜_{n+m} ⟶ 𝒜_n` from the adic bound, and
  Stacks 0AGK for the tower from Stacks 0AGG and the adic bound.

## References

* [Stacks Project, Tag 0AGK](https://stacks.math.columbia.edu/tag/0AGK)
* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
-/

/-!
## Implementation notes

The statements below are shaped so that the kernel's check of each instance stays cheap; three
shapes made it time out, and are avoided.

* Restriction maps abbreviated: the restrictions `𝒜_k ⟶ f_* 𝒪_{X'}` and `𝒜_k ⟶ 𝒪_{Z_{k+1}}` are
  written out as `pushforwardRingMap` of `modificationToStage` and `memberToStage` everywhere.
  The equalizer condition stated through abbreviations for them does not pass the kernel; the
  same statement written out does.
* Lemmas over an arbitrary `X : AlgebraicSpaces` instantiated at `T.targetSpace`: their sections
  are typed through `X.1` and `X.2`, the concrete statements through `T.X` and `T.hX`, and
  matching the two inside the large direct-image terms does not pass. The element-level lemmas
  used on concrete morphisms (`ClosedSubspaceSystem.pushforwardRingMap_app_comm`,
  `ClosedSubspaceSystem.pushforwardRingMap_app_sub_algebraMap_eq_zero`,
  `ClosedSubspaceSystem.pushforwardRingMap_app_algebraMap_add_sub_eq_zero`,
  `ClosedSubspaceSystem.exists_algebraMap_eq_of_locally`) are therefore stated over
  `T.targetSpace` for arbitrary morphisms over it, and only instantiated.
* `sub_eq_zero` on the sections of a concrete direct-image algebra: it compares the additive-group
  and the ring structures there. The local step is stated as the vanishing of a difference, and
  the conversion happens inside `ClosedSubspaceSystem.exists_algebraMap_eq_of_locally`, on a
  variable algebra.

With these shapes the base comparison `AlgebraicGeometry.Space.pushforwardSquareMap` for the
square `X' ×_X Z_k ⟶ X' ⟶ X ⟵ Z_k` is not needed: the equalizer condition is
`ClosedSubspaceSystem.crossToModification_comp`, pushed through `pushforwardRingMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Restriction and gluing -/

/-- A morphism of sheaves of rings commutes with restriction, on elements. -/
theorem sheafHom_app_map {Y : AlgebraicSpaces B S hS}
    {C C' : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}} (φ : C ⟶ C')
    {V W : SmallEtale B S hS Y.1} (g : W ⟶ V) (x : C.obj.obj (op V)) :
    φ.hom.app (op W) (C.obj.map g.op x) = C'.obj.map g.op (φ.hom.app (op V) x) := by
  simpa only [CommRingCat.comp_apply] using ConcreteCategory.congr_hom (φ.hom.naturality g.op) x

/-- The map induced on direct images by a morphism over `X` respects the structure maps. -/
theorem pushforwardRingMap_app_algebraMap {X : AlgebraicSpaces B S hS} {Y Z : Over X}
    (h : Y ⟶ Z) (U : (SmallEtale B S hS X.1)ᵒᵖ) (r : (structureSheaf B S hS X.1 X.2).obj.obj U) :
    (pushforwardRingMap B S hS h).hom.app U ((pushforwardAlgebra B S hS Z).algebraMap U r) =
      (pushforwardAlgebra B S hS Y).algebraMap U r :=
  (pushforwardAlgebraMap B S hS h).comm U r

/-- A composite of morphisms of sheaves of rings, on elements. -/
theorem sheafHom_comp_app_apply {Y : AlgebraicSpaces B S hS}
    {C C' C'' : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}} (φ : C ⟶ C')
    (ψ : C' ⟶ C'') (V : (SmallEtale B S hS Y.1)ᵒᵖ) (x : C.obj.obj V) :
    (φ ≫ ψ).hom.app V x = ψ.hom.app V (φ.hom.app V x) :=
  rfl

/-- Restriction along a composite, on elements. -/
theorem sheaf_map_comp_apply {Y : AlgebraicSpaces B S hS}
    (C : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u})
    {V W W' : SmallEtale B S hS Y.1} (g : W ⟶ V) (g' : W' ⟶ W) (x : C.obj.obj (op V)) :
    C.obj.map (g' ≫ g).op x = C.obj.map g'.op (C.obj.map g.op x) := by
  rw [op_comp, Functor.map_comp, CommRingCat.comp_apply]

/-- **Gluing through an injective morphism of sheaves of rings.** If `e : A ⟶ C` is injective on
every chart and a section `x` of `C` lies, locally on a covering sieve, in the image of `e`, then
it lies in the image of `e`. -/
theorem exists_eq_of_locally_mem_range {Y : AlgebraicSpaces B S hS}
    {A C : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}} (e : A ⟶ C)
    (he : ∀ U, Function.Injective (e.hom.app U)) {V : SmallEtale B S hS Y.1}
    (x : C.obj.obj (op V)) (R : Sieve V) (hR : R ∈ SmallEtale.topology B S hS Y.1 V)
    (h : ∀ ⦃W⦄ (g : W ⟶ V), R g → ∃ r, e.hom.app (op W) r = C.obj.map g.op x) :
    ∃ r, e.hom.app (op V) r = x := by
  choose r hr using h
  have hA : Presieve.IsSheaf (SmallEtale.topology B S hS Y.1) (A.obj ⋙ forget CommRingCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat)).obj A).property
  have hC : Presieve.IsSheaf (SmallEtale.topology B S hS Y.1) (C.obj ⋙ forget CommRingCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat)).obj C).property
  let fam : Presieve.FamilyOfElements (A.obj ⋙ forget CommRingCat) R.arrows :=
    fun W g hg => r g hg
  have hcomp : fam.Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hw
    apply he (op Z)
    change e.hom.app (op Z) (A.obj.map g₁.op (r f₁ h₁)) =
      e.hom.app (op Z) (A.obj.map g₂.op (r f₂ h₂))
    rw [sheafHom_app_map, sheafHom_app_map, hr, hr, ← sheaf_map_comp_apply,
      ← sheaf_map_comp_apply, hw]
  obtain ⟨t, ht, -⟩ := hA R hR fam hcomp
  refine ⟨t, (hC R hR).isSeparatedFor.ext fun W g hg => ?_⟩
  change C.obj.map g.op (e.hom.app (op V) t) = C.obj.map g.op x
  rw [← sheafHom_app_map]
  exact (congrArg (e.hom.app (op W)) (ht g hg)).trans (hr g hg)

namespace CoequalizerGlueSituation

variable (T : CoequalizerGlueSituation.{u})

/-! ### The spaces `X' ×_X Z_k` -/

/-- `X'_k = X' ×_X Z_{k+1}`, the presheaf fibre product. -/
abbrev crossSpace (k : ℕ) : AlgebraicSpaces T.B T.S T.hS :=
  AlgebraicSpaces.fiberProduct T.B T.S T.hS
    (ObjectProperty.homMk T.f : T.modificationSpace ⟶ T.targetSpace)
    (T.neighbourhoodSystem.toTarget k)

/-- The projection `X'_k ⟶ X'`. -/
abbrev crossFst (k : ℕ) : T.crossSpace k ⟶ T.modificationSpace :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The projection `X'_k ⟶ Z_{k+1}`. -/
abbrev crossSnd (k : ℕ) : T.crossSpace k ⟶ T.neighbourhoodSystem.space k :=
  ObjectProperty.homMk (pullback.snd _ _)

/-- The square `X'_k ⟶ X' ⟶ X` and `X'_k ⟶ Z_{k+1} ⟶ X` commutes. -/
theorem crossFst_comp (k : ℕ) :
    T.crossFst k ≫ (ObjectProperty.homMk T.f : T.modificationSpace ⟶ T.targetSpace) =
      T.crossSnd k ≫ T.neighbourhoodSystem.toTarget k :=
  ObjectProperty.hom_ext _ pullback.condition

/-- `X'_k` as an algebraic space over `X`. -/
abbrev crossOver (k : ℕ) : Over T.targetSpace :=
  Over.mk (T.crossFst k ≫ (ObjectProperty.homMk T.f : T.modificationSpace ⟶ T.targetSpace))

/-- The projection `X'_k ⟶ X'`, over `X`. -/
abbrev crossToModification (k : ℕ) : T.crossOver k ⟶ T.modificationOver :=
  Over.homMk (T.crossFst k)

/-- The projection `X'_k ⟶ Z_{k+1}`, over `X`. -/
abbrev crossToMember (k : ℕ) : T.crossOver k ⟶ T.neighbourhoodSystem.memberOver k :=
  Over.homMk (T.crossSnd k) (T.crossFst_comp k).symm

/-- **The adic bound for `f : X' ⟶ X` along the infinitesimal neighbourhoods of `Z`**: there is a
`c` such that for `k ≥ c` every section of the kernel of restriction
`f_* 𝒪_{X'} ⟶ (X' ×_X Z_{k+1} ⟶ X)_* 𝒪` is, locally on `X`, the image under `f♯` of a section of
`𝓘ᵏ⁺¹⁻ᶜ`. -/
def AdicKernelBound : Prop :=
  ∃ c : ℕ, ∀ k : ℕ, c ≤ k → ∀ (V : SmallEtale T.B T.S T.hS T.X)
    (a : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.obj (op V)),
    (pushforwardRingMap T.B T.S T.hS (T.crossToModification k)).hom.app (op V) a = 0 →
    ∃ R : Sieve V, R ∈ SmallEtale.topology T.B T.S T.hS T.X V ∧
      ∀ ⦃W⦄ (g : W ⟶ V), R g →
        ∃ s : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W),
          s ∈ (Stacks.Sites.idealPow (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)
            T.closedIdeal (k + 1 - c)).obj (op W) ∧
          (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.map g.op a =
            (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op W) s

namespace ClosedSubspaceSystem

variable {T} (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (T.neighbourhoodSystem.glueMapAt n))

/-- **The equalizer condition on `X' ×_X Z_{k+1}`**: the two morphisms `X'_k ⟶ X_k`, through `X'`
and through `Z_{k+1}`, agree, because together they land in the kernel pair of
`Y_k ⟶ X`, which the quotient map coequalizes. -/
theorem crossToModification_comp (k : ℕ) :
    T.crossToModification k ≫ T.neighbourhoodSystem.modificationToStage D k =
      T.crossToMember k ≫ T.neighbourhoodSystem.memberToStage D k := by
  refine Over.OverMorphism.ext ?_
  change T.crossFst k ≫ coprod.inl ≫ (D k).π = T.crossSnd k ≫ coprod.inr ≫ (D k).π
  let L : T.crossSpace k ⟶ pullback (T.neighbourhoodSystem.glueMapAt k)
      (T.neighbourhoodSystem.glueMapAt k) :=
    pullback.lift (T.crossFst k ≫ coprod.inl) (T.crossSnd k ≫ coprod.inr) (by
      rw [Category.assoc, Category.assoc, glueMapAt, coprod.inl_desc, coprod.inr_desc,
        T.crossFst_comp])
  have h := congrArg (fun q => L ≫ q) (D k).equalizes
  simp only [L, ← Category.assoc, pullback.lift_fst, pullback.lift_snd] at h
  simpa only [Category.assoc] using h

/-- The inclusion `Z_{n+1} ⟶ Z_{n+m+1}`. -/
def memberStep (n : ℕ) : ∀ m : ℕ,
    T.neighbourhoodSystem.space n ⟶ T.neighbourhoodSystem.space (n + m)
  | 0 => 𝟙 _
  | m + 1 => memberStep n m ≫ T.neighbourhoodSystem.step (n + m)

/-- The inclusion `Z_{n+1} ⟶ Z_{n+m+1}` followed by `Z_{n+m+1} ⟶ X` is `Z_{n+1} ⟶ X`. -/
theorem memberStep_comp_toTarget (n : ℕ) : ∀ m : ℕ,
    memberStep n m ≫ T.neighbourhoodSystem.toTarget (n + m) = T.neighbourhoodSystem.toTarget n
  | 0 => Category.id_comp _
  | m + 1 => by
    rw [memberStep, Category.assoc]
    change memberStep n m ≫ T.neighbourhoodSystem.step (n + m) ≫
      T.neighbourhoodSystem.toTarget (n + m + 1) = _
    rw [T.neighbourhoodSystem.step_comp_toTarget, memberStep_comp_toTarget n m]

/-- The composite `X' ⟶ X' ⨿ Z_{n+1} ⟶ X_n ⟶ X_{n+m}` is the morphism
`X' ⟶ X' ⨿ Z_{n+m+1} ⟶ X_{n+m}`. -/
theorem inl_π_towerTransition (n : ℕ) : ∀ m : ℕ,
    coprod.inl ≫ (D n).π ≫ T.neighbourhoodSystem.towerTransition D n m =
      coprod.inl ≫ (D (n + m)).π
  | 0 => by rw [towerTransition, Category.comp_id]; rfl
  | m + 1 => by
    change coprod.inl ≫ (D n).π ≫ (T.neighbourhoodSystem.towerTransition D n m ≫
      T.neighbourhoodSystem.towerMap D (n + m)) = _
    rw [← Category.assoc (D n).π, ← Category.assoc coprod.inl, inl_π_towerTransition n m,
      Category.assoc, π_comp_towerMap, sourceStep, coprod.inl_map_assoc, Category.id_comp]
    rfl

/-- The composite `Z_{n+1} ⟶ X' ⨿ Z_{n+1} ⟶ X_n ⟶ X_{n+m}` is the morphism
`Z_{n+1} ⟶ Z_{n+m+1} ⟶ X' ⨿ Z_{n+m+1} ⟶ X_{n+m}`. -/
theorem inr_π_towerTransition (n : ℕ) : ∀ m : ℕ,
    coprod.inr ≫ (D n).π ≫ T.neighbourhoodSystem.towerTransition D n m =
      memberStep n m ≫ coprod.inr ≫ (D (n + m)).π
  | 0 => by rw [towerTransition, Category.comp_id, memberStep, Category.id_comp]; rfl
  | m + 1 => by
    change coprod.inr ≫ (D n).π ≫ (T.neighbourhoodSystem.towerTransition D n m ≫
      T.neighbourhoodSystem.towerMap D (n + m)) = _
    rw [← Category.assoc (D n).π, ← Category.assoc coprod.inr, inr_π_towerTransition n m,
      Category.assoc, Category.assoc, π_comp_towerMap, sourceStep, coprod.inr_map_assoc]
    change _ = (memberStep n m ≫ T.neighbourhoodSystem.step (n + m)) ≫ _
    rw [Category.assoc]
    rfl

/-- `X' ⟶ X_n ⟶ X_{n+m}` is `X' ⟶ X_{n+m}`, over `X`. -/
theorem modificationToStage_comp_towerTransitionOver (n m : ℕ) :
    T.neighbourhoodSystem.modificationToStage D n ≫
        T.neighbourhoodSystem.towerTransitionOver D n m =
      T.neighbourhoodSystem.modificationToStage D (n + m) :=
  Over.OverMorphism.ext (by
    change (coprod.inl ≫ (D n).π) ≫ T.neighbourhoodSystem.towerTransition D n m = _
    rw [Category.assoc, inl_π_towerTransition]
    rfl)

/-- The inclusion `Z_{n+1} ⟶ Z_{n+m+1}`, over `X`. -/
abbrev memberStepOver (n m : ℕ) :
    T.neighbourhoodSystem.memberOver n ⟶ T.neighbourhoodSystem.memberOver (n + m) :=
  Over.homMk (memberStep n m) (memberStep_comp_toTarget n m)

/-- `Z_{n+1} ⟶ X_n ⟶ X_{n+m}` is `Z_{n+1} ⟶ Z_{n+m+1} ⟶ X_{n+m}`, over `X`. -/
theorem memberToStage_comp_towerTransitionOver (n m : ℕ) :
    T.neighbourhoodSystem.memberToStage D n ≫ T.neighbourhoodSystem.towerTransitionOver D n m =
      memberStepOver n m ≫ T.neighbourhoodSystem.memberToStage D (n + m) :=
  Over.OverMorphism.ext (by
    change (coprod.inr ≫ (D n).π) ≫ T.neighbourhoodSystem.towerTransition D n m =
      memberStep n m ≫ coprod.inr ≫ (D (n + m)).π
    rw [Category.assoc, inr_π_towerTransition])

/-- The direct-image map of a composite, on elements. -/
private theorem pushforwardRingMap_comp_app_apply (T : CoequalizerGlueSituation.{u})
    {Y₁ Y₂ Y₃ : Over T.targetSpace} (f : Y₁ ⟶ Y₂)
    (g : Y₂ ⟶ Y₃) (V : SmallEtale T.B T.S T.hS T.X)
    (b : (pushforwardAlgebra T.B T.S T.hS Y₃).right.obj.obj (op V)) :
    (pushforwardRingMap T.B T.S T.hS (f ≫ g)).hom.app (op V) b =
      (pushforwardRingMap T.B T.S T.hS f).hom.app (op V)
        ((pushforwardRingMap T.B T.S T.hS g).hom.app (op V) b) := by
  rw [pushforwardRingMap_comp, sheafHom_comp_app_apply]

variable (T) in
/-- Pushing a commutative square of morphisms over `X` through direct images, on elements. -/
theorem pushforwardRingMap_app_comm {Y₁ Y₂ Y₃ Y₄ : Over T.targetSpace} (f₁ : Y₁ ⟶ Y₂)
    (g₁ : Y₂ ⟶ Y₄) (f₂ : Y₁ ⟶ Y₃) (g₂ : Y₃ ⟶ Y₄) (h : f₁ ≫ g₁ = f₂ ≫ g₂)
    (V : SmallEtale T.B T.S T.hS T.X)
    (b : (pushforwardAlgebra T.B T.S T.hS Y₄).right.obj.obj (op V)) :
    (pushforwardRingMap T.B T.S T.hS f₁).hom.app (op V)
        ((pushforwardRingMap T.B T.S T.hS g₁).hom.app (op V) b) =
      (pushforwardRingMap T.B T.S T.hS f₂).hom.app (op V)
        ((pushforwardRingMap T.B T.S T.hS g₂).hom.app (op V) b) := by
  rw [← pushforwardRingMap_comp_app_apply T, ← pushforwardRingMap_comp_app_apply T, h]

variable (T) in
/-- **The difference step on a commutative square.** Let `f₁ ≫ g₁ = f₂ ≫ g₂` be a commutative
square over `X` with `g₁ : Y₂ ⟶ Y₄` and `g₂ : Y₃ ⟶ Y₄`. If the restriction of `b ∈ (Y₄)_* 𝒪` to
`Y₃` is the structure image of `t` over `W`, then the restriction of `b` to `Y₂` minus the
structure image of `t` is killed by `f₁`. -/
theorem pushforwardRingMap_app_sub_algebraMap_eq_zero {Y₁ Y₂ Y₃ Y₄ : Over T.targetSpace}
    (f₁ : Y₁ ⟶ Y₂) (g₁ : Y₂ ⟶ Y₄) (f₂ : Y₁ ⟶ Y₃) (g₂ : Y₃ ⟶ Y₄)
    (h : f₁ ≫ g₁ = f₂ ≫ g₂) {V W : SmallEtale T.B T.S T.hS T.X} (g : W ⟶ V)
    (b : (pushforwardAlgebra T.B T.S T.hS Y₄).right.obj.obj (op V))
    (t : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W))
    (ht : (pushforwardAlgebra T.B T.S T.hS Y₃).right.obj.map g.op
        ((pushforwardRingMap T.B T.S T.hS g₂).hom.app (op V) b) =
      (pushforwardAlgebra T.B T.S T.hS Y₃).algebraMap (op W) t) :
    (pushforwardRingMap T.B T.S T.hS f₁).hom.app (op W)
      ((pushforwardAlgebra T.B T.S T.hS Y₂).right.obj.map g.op
          ((pushforwardRingMap T.B T.S T.hS g₁).hom.app (op V) b) -
        (pushforwardAlgebra T.B T.S T.hS Y₂).algebraMap (op W) t) = 0 := by
  rw [map_sub, pushforwardRingMap_app_algebraMap, sheafHom_app_map,
    pushforwardRingMap_app_comm T f₁ g₁ f₂ g₂ h V, ← sheafHom_app_map, ht,
    pushforwardRingMap_app_algebraMap, sub_self]

variable (T) in
/-- **The difference step along a transition.** Let `μ ≫ τ = σ ≫ μ'` be a commutative square
over `X`, with `τ : P ⟶ P'`, `μ : M ⟶ P` and `μ' : M' ⟶ P'`. If the restriction of
`b ∈ P'_* 𝒪` to `M'` is the structure image of `t` over `W`, and `s` is killed by
`𝒪_X ⟶ M_* 𝒪`, then the structure image of `t + s` minus the image of `b` in `P_* 𝒪` is killed
by `μ` over `W' ⟶ W`. -/
theorem pushforwardRingMap_app_algebraMap_add_sub_eq_zero {M M' P P' : Over T.targetSpace}
    (μ : M ⟶ P) (τ : P ⟶ P') (σ : M ⟶ M') (μ' : M' ⟶ P')
    (h : μ ≫ τ = σ ≫ μ') {V W W' : SmallEtale T.B T.S T.hS T.X} (g : W ⟶ V) (g' : W' ⟶ W)
    (b : (pushforwardAlgebra T.B T.S T.hS P').right.obj.obj (op V))
    (t : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W))
    (s : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W'))
    (ht : (pushforwardAlgebra T.B T.S T.hS M').right.obj.map g.op
        ((pushforwardRingMap T.B T.S T.hS μ').hom.app (op V) b) =
      (pushforwardAlgebra T.B T.S T.hS M').algebraMap (op W) t)
    (hs : (pushforwardAlgebra T.B T.S T.hS M).algebraMap (op W') s = 0) :
    (pushforwardRingMap T.B T.S T.hS μ).hom.app (op W')
      ((pushforwardAlgebra T.B T.S T.hS P).algebraMap (op W')
          ((structureSheaf T.B T.S T.hS T.X T.hX).obj.map g'.op t + s) -
        (pushforwardAlgebra T.B T.S T.hS P).right.obj.map (g' ≫ g).op
          ((pushforwardRingMap T.B T.S T.hS τ).hom.app (op V) b)) = 0 := by
  rw [map_sub, pushforwardRingMap_app_algebraMap, sheafHom_app_map,
    pushforwardRingMap_app_comm T μ τ σ μ' h V,
    ← sheafHom_app_map (pushforwardRingMap T.B T.S T.hS σ) (g' ≫ g), sheaf_map_comp_apply, ht,
    (pushforwardAlgebra T.B T.S T.hS M').algebraMap_natural, pushforwardRingMap_app_algebraMap,
    map_add, hs, add_zero, sub_self]

variable (T) in
/-- Gluing a section of `P_* 𝒪` which lies, locally on a covering sieve, in the image of an
injective structure map `𝒪_X ⟶ P_* 𝒪`, the local condition being the vanishing of a
difference. -/
theorem exists_algebraMap_eq_of_locally (P : Over T.targetSpace)
    (hinj : ∀ V : SmallEtale T.B T.S T.hS T.X,
      Function.Injective ((pushforwardAlgebra T.B T.S T.hS P).algebraMap (op V)))
    {V : SmallEtale T.B T.S T.hS T.X}
    (x : (pushforwardAlgebra T.B T.S T.hS P).right.obj.obj (op V))
    (R : Sieve V) (hR : R ∈ SmallEtale.topology T.B T.S T.hS T.X V)
    (h : ∀ ⦃W⦄ (g : W ⟶ V), R g → ∃ r, (pushforwardAlgebra T.B T.S T.hS P).algebraMap (op W) r -
      (pushforwardAlgebra T.B T.S T.hS P).right.obj.map g.op x = 0) :
    ∃ r, (pushforwardAlgebra T.B T.S T.hS P).algebraMap (op V) r = x :=
  exists_eq_of_locally_mem_range (Y := T.targetSpace)
    (AlgebraSheaf.hom (pushforwardAlgebra T.B T.S T.hS P)) (fun U => hinj U.unop) x R hR
    fun _ g hg => (h g hg).imp fun _ hr => sub_eq_zero.1 hr

/-- A section of `𝓘ⁿ⁺¹` is killed by `𝒪_X ⟶ 𝒪_{Z_{n+1}}`. -/
theorem algebraMap_memberOver_eq_zero (n : ℕ) {W : SmallEtale T.B T.S T.hS T.X}
    (s : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W))
    (hs : s ∈ (T.neighbourhoodIdeal n).obj (op W)) :
    (pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.memberOver n)).algebraMap (op W) s =
      0 := by
  rw [← T.kernelIdealSheaf_neighbourhoodSystem_toTarget n] at hs
  exact (structureSharp_app_eq_zero_iff (T.neighbourhoodSystem.memberOver n) (op W) s).1 hs

end ClosedSubspaceSystem

section Local

variable (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS)
  (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (T.neighbourhoodSystem.glueMapAt n))

/-- **The equalizer condition on `X' ×_X Z_{k+1}`, on sections**: the two restrictions of a
section `b` of `𝒜_k` to `X'_k`, through `X'` and through `Z_{k+1}`, agree. -/
theorem restrict_cross_eq (k : ℕ) {V : SmallEtale T.B T.S T.hS T.X}
    (b : (pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.stageOver D k)).right.obj.obj
      (op V)) :
    (pushforwardRingMap T.B T.S T.hS (T.crossToModification k)).hom.app (op V)
        ((pushforwardRingMap T.B T.S T.hS (T.neighbourhoodSystem.modificationToStage D k)).hom.app
          (op V) b) =
      (pushforwardRingMap T.B T.S T.hS (T.crossToMember k)).hom.app (op V)
        ((pushforwardRingMap T.B T.S T.hS (T.neighbourhoodSystem.memberToStage D k)).hom.app
          (op V) b) :=
  ClosedSubspaceSystem.pushforwardRingMap_app_comm T _ _ _ _
    (ClosedSubspaceSystem.crossToModification_comp D k) V b

/-- If the restriction of `b ∈ 𝒜_k` to `Z_{k+1}` is `i♯ t` over `W`, then the restriction of `b`
to `X'` minus `f♯ t` lies in the kernel of restriction to `X' ×_X Z_{k+1}`. -/
theorem crossToModification_sub_eq_zero (k : ℕ) {V W : SmallEtale T.B T.S T.hS T.X}
    (b : (pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.stageOver D k)).right.obj.obj
      (op V))
    (g : W ⟶ V) (t : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W))
    (ht : (pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.memberOver k)).right.obj.map
        g.op ((pushforwardRingMap T.B T.S T.hS
          (T.neighbourhoodSystem.memberToStage D k)).hom.app (op V) b) =
      (pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.memberOver k)).algebraMap (op W) t) :
    (pushforwardRingMap T.B T.S T.hS (T.crossToModification k)).hom.app (op W)
      ((pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.map g.op
          ((pushforwardRingMap T.B T.S T.hS
            (T.neighbourhoodSystem.modificationToStage D k)).hom.app (op V) b) -
        (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op W) t) = 0 :=
  ClosedSubspaceSystem.pushforwardRingMap_app_sub_algebraMap_eq_zero T _ _ _ _
    (ClosedSubspaceSystem.crossToModification_comp D k) g b t ht

/-- The restriction of the difference to `X'` vanishes. -/
theorem restrictModification_sub_eq_zero (n c : ℕ) {V W W' : SmallEtale T.B T.S T.hS T.X}
    (b : (pushforwardAlgebra T.B T.S T.hS
      (T.neighbourhoodSystem.stageOver D (n + c))).right.obj.obj (op V))
    (g : W ⟶ V) (g' : W' ⟶ W) (t : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W))
    (s : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W'))
    (hds : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.map g'.op
        ((pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.map g.op
          ((pushforwardRingMap T.B T.S T.hS
            (T.neighbourhoodSystem.modificationToStage D (n + c))).hom.app (op V) b) -
        (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op W) t) =
      (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op W') s) :
    (pushforwardRingMap T.B T.S T.hS (T.neighbourhoodSystem.modificationToStage D n)).hom.app
      (op W')
      ((pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.stageOver D n)).algebraMap (op W')
          ((structureSheaf T.B T.S T.hS T.X T.hX).obj.map g'.op t + s) -
        (pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.stageOver D n)).right.obj.map
          (g' ≫ g).op ((pushforwardRingMap T.B T.S T.hS
            (T.neighbourhoodSystem.towerTransitionOver D n c)).hom.app (op V) b)) = 0 := by
  have L2 := ClosedSubspaceSystem.pushforwardRingMap_comp_app_apply T
    (T.neighbourhoodSystem.modificationToStage D n)
    (T.neighbourhoodSystem.towerTransitionOver D n c) V b
  rw [ClosedSubspaceSystem.modificationToStage_comp_towerTransitionOver] at L2
  rw [map_sub, pushforwardRingMap_app_algebraMap, sheafHom_app_map, ← L2, map_add,
    ← (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap_natural, ← hds,
    sheaf_map_comp_apply, map_sub]
  ring

/-- The restriction of the difference to `Z_{n+1}` vanishes, once `s` dies on `Z_{n+1}`. -/
theorem restrictMember_sub_eq_zero (n c : ℕ) {V W W' : SmallEtale T.B T.S T.hS T.X}
    (b : (pushforwardAlgebra T.B T.S T.hS
      (T.neighbourhoodSystem.stageOver D (n + c))).right.obj.obj (op V))
    (g : W ⟶ V) (g' : W' ⟶ W) (t : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W))
    (s : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W'))
    (ht : (pushforwardAlgebra T.B T.S T.hS
        (T.neighbourhoodSystem.memberOver (n + c))).right.obj.map g.op
          ((pushforwardRingMap T.B T.S T.hS
            (T.neighbourhoodSystem.memberToStage D (n + c))).hom.app (op V) b) =
      (pushforwardAlgebra T.B T.S T.hS
        (T.neighbourhoodSystem.memberOver (n + c))).algebraMap (op W) t)
    (hs : (pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.memberOver n)).algebraMap
      (op W') s = 0) :
    (pushforwardRingMap T.B T.S T.hS (T.neighbourhoodSystem.memberToStage D n)).hom.app (op W')
      ((pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.stageOver D n)).algebraMap (op W')
          ((structureSheaf T.B T.S T.hS T.X T.hX).obj.map g'.op t + s) -
        (pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.stageOver D n)).right.obj.map
          (g' ≫ g).op ((pushforwardRingMap T.B T.S T.hS
            (T.neighbourhoodSystem.towerTransitionOver D n c)).hom.app (op V) b)) = 0 :=
  ClosedSubspaceSystem.pushforwardRingMap_app_algebraMap_add_sub_eq_zero T _ _ _ _
    (ClosedSubspaceSystem.memberToStage_comp_towerTransitionOver D n c) g g' b t s ht hs

/-- A section of `𝒪_{Z_{k+1}}` is, locally on `X`, the image of a section of `𝒪_X`
(Stacks 03MB). -/
theorem exists_algebraMap_memberOver_eq (k : ℕ) {V : SmallEtale T.B T.S T.hS T.X}
    (z : (pushforwardAlgebra T.B T.S T.hS
      (T.neighbourhoodSystem.memberOver k)).right.obj.obj (op V)) :
    ∃ R : Sieve V, R ∈ SmallEtale.topology T.B T.S T.hS T.X V ∧
      ∀ ⦃W⦄ (g : W ⟶ V), R g →
        ∃ t : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W),
          (pushforwardAlgebra T.B T.S T.hS
            (T.neighbourhoodSystem.memberOver k)).right.obj.map g.op z =
            (pushforwardAlgebra T.B T.S T.hS
              (T.neighbourhoodSystem.memberOver k)).algebraMap (op W) t := by
  have hls := isLocallySurjective_structureSharp T.B T.S T.hS (T.neighbourhoodSystem.toTarget k)
    (T.neighbourhoodSystem.isClosedImmersion_toTarget k)
  refine ⟨_, Presheaf.imageSieve_mem (SmallEtale.topology T.B T.S T.hS T.X)
    (structureSharp T.B T.S T.hS (T.neighbourhoodSystem.toTarget k)).hom (U := op V) z,
    fun W g ⟨t, ht⟩ => ⟨t, ?_⟩⟩
  exact ht.symm.trans (structureSharp_app_eq_structureSharpCommRing_app _ _ _)

include hAGG in
/-- **The local step**: with `t` lifting the restriction of `b ∈ 𝒜_{n+c}` to `Z_{n+c+1}` and `s`
a section of `𝓘ⁿ⁺¹` with `f♯ s` the restriction of `b` to `X'` minus `f♯ t`, the section `t + s`
of `𝒪_X` maps to the image of `b` in `𝒜_n` (stated as the vanishing of the difference). -/
theorem algebraMap_add_sub_towerTransition_eq_zero (n c : ℕ) {V W W' : SmallEtale T.B T.S T.hS T.X}
    (b : (pushforwardAlgebra T.B T.S T.hS
      (T.neighbourhoodSystem.stageOver D (n + c))).right.obj.obj (op V))
    (g : W ⟶ V) (g' : W' ⟶ W) (t : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W))
    (s : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W'))
    (ht : (pushforwardAlgebra T.B T.S T.hS
        (T.neighbourhoodSystem.memberOver (n + c))).right.obj.map g.op
          ((pushforwardRingMap T.B T.S T.hS
            (T.neighbourhoodSystem.memberToStage D (n + c))).hom.app (op V) b) =
      (pushforwardAlgebra T.B T.S T.hS
        (T.neighbourhoodSystem.memberOver (n + c))).algebraMap (op W) t)
    (hds : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.map g'.op
        ((pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.map g.op
          ((pushforwardRingMap T.B T.S T.hS
            (T.neighbourhoodSystem.modificationToStage D (n + c))).hom.app (op V) b) -
        (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op W) t) =
      (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op W') s)
    (hs : s ∈ (T.neighbourhoodIdeal n).obj (op W')) :
    (pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.stageOver D n)).algebraMap (op W')
        ((structureSheaf T.B T.S T.hS T.X T.hX).obj.map g'.op t + s) -
      (pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.stageOver D n)).right.obj.map
        (g' ≫ g).op ((pushforwardRingMap T.B T.S T.hS
          (T.neighbourhoodSystem.towerTransitionOver D n c)).hom.app (op V) b) = 0 :=
  T.neighbourhoodSystem.eq_zero_of_restrictions_eq_zero D hAGG n W' _
    (restrictModification_sub_eq_zero T D n c b g g' t s hds)
    (restrictMember_sub_eq_zero T D n c b g g' t s ht
      (ClosedSubspaceSystem.algebraMap_memberOver_eq_zero n s hs))

include hAGG in
/-- **The local step, on a covering sieve**: given the adic bound with constant `c` and a lift `t`
of the restriction of `b ∈ 𝒜_{n+c}` to `Z_{n+c+1}` over `W`, the image of `b` in `𝒜_n` lies,
locally on `W`, in the image of `𝒪_X`. -/
theorem exists_sieve_algebraMap_eq_towerTransition (c : ℕ)
    (hc : ∀ k : ℕ, c ≤ k → ∀ (V : SmallEtale T.B T.S T.hS T.X)
      (a : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.obj (op V)),
      (pushforwardRingMap T.B T.S T.hS (T.crossToModification k)).hom.app (op V) a = 0 →
      ∃ R : Sieve V, R ∈ SmallEtale.topology T.B T.S T.hS T.X V ∧
        ∀ ⦃W⦄ (g : W ⟶ V), R g →
          ∃ s : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W),
            s ∈ (Stacks.Sites.idealPow (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)
              T.closedIdeal (k + 1 - c)).obj (op W) ∧
            (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.map g.op a =
              (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op W) s)
    (n : ℕ) {V W : SmallEtale T.B T.S T.hS T.X}
    (b : (pushforwardAlgebra T.B T.S T.hS
      (T.neighbourhoodSystem.stageOver D (n + c))).right.obj.obj (op V))
    (g : W ⟶ V) (t : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W))
    (ht : (pushforwardAlgebra T.B T.S T.hS
        (T.neighbourhoodSystem.memberOver (n + c))).right.obj.map g.op
          ((pushforwardRingMap T.B T.S T.hS
            (T.neighbourhoodSystem.memberToStage D (n + c))).hom.app (op V) b) =
      (pushforwardAlgebra T.B T.S T.hS
        (T.neighbourhoodSystem.memberOver (n + c))).algebraMap (op W) t) :
    ∃ R' : Sieve W, R' ∈ SmallEtale.topology T.B T.S T.hS T.X W ∧
      ∀ ⦃W'⦄ (g' : W' ⟶ W), R' g' →
        ∃ r, (pushforwardAlgebra T.B T.S T.hS
            (T.neighbourhoodSystem.stageOver D n)).algebraMap (op W') r -
          (pushforwardAlgebra T.B T.S T.hS
            (T.neighbourhoodSystem.stageOver D n)).right.obj.map (g' ≫ g).op
            ((pushforwardRingMap T.B T.S T.hS
              (T.neighbourhoodSystem.towerTransitionOver D n c)).hom.app (op V) b) = 0 := by
  obtain ⟨R', hR', hs⟩ := hc (n + c) (Nat.le_add_left c n) W _
    (crossToModification_sub_eq_zero T D (n + c) b g t ht)
  refine ⟨R', hR', fun W' g' hg' => ?_⟩
  obtain ⟨s, hsI, hds⟩ := hs g' hg'
  have hsI' : s ∈ (T.neighbourhoodIdeal n).obj (op W') := by
    rwa [show n + c + 1 - c = n + 1 by lia] at hsI
  exact ⟨_, T.algebraMap_add_sub_towerTransition_eq_zero hAGG D n c b g g' t s ht hds hsI'⟩

include hAGG in
/-- **The image of `𝒜_{n+c} ⟶ 𝒜_n` lies in that of `𝒪_X`**, given the adic bound with constant
`c` and the injectivity of `𝒪_X ⟶ 𝒜_n`. -/
theorem rangeLeStructureAt_of_kernelBound (c : ℕ)
    (hc : ∀ k : ℕ, c ≤ k → ∀ (V : SmallEtale T.B T.S T.hS T.X)
      (a : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.obj (op V)),
      (pushforwardRingMap T.B T.S T.hS (T.crossToModification k)).hom.app (op V) a = 0 →
      ∃ R : Sieve V, R ∈ SmallEtale.topology T.B T.S T.hS T.X V ∧
        ∀ ⦃W⦄ (g : W ⟶ V), R g →
          ∃ s : (structureSheaf T.B T.S T.hS T.X T.hX).obj.obj (op W),
            s ∈ (Stacks.Sites.idealPow (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)
              T.closedIdeal (k + 1 - c)).obj (op W) ∧
            (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.map g.op a =
              (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op W) s)
    (n : ℕ) (hinj : ∀ V : SmallEtale T.B T.S T.hS T.X, Function.Injective
      ((pushforwardAlgebra T.B T.S T.hS (T.neighbourhoodSystem.stageOver D n)).algebraMap (op V))) :
    T.neighbourhoodSystem.RangeLeStructureAt D n c := by
  intro V b
  obtain ⟨R, hR, hRt⟩ := T.exists_algebraMap_memberOver_eq (n + c)
    ((pushforwardRingMap T.B T.S T.hS
      (T.neighbourhoodSystem.memberToStage D (n + c))).hom.app (op V) b)
  choose t ht using hRt
  choose R' hR' hr using fun W (g : W ⟶ V) (hg : R g) =>
    T.exists_sieve_algebraMap_eq_towerTransition hAGG D c hc n b g (t g hg) (ht g hg)
  refine ClosedSubspaceSystem.exists_algebraMap_eq_of_locally T _ hinj _
    (Sieve.bind R.arrows fun _ g hg => R' _ g hg)
    (GrothendieckTopology.bind_covering _ (R := fun _ g hg => R' _ g hg) hR
      fun _ g hg => hR' _ g hg) ?_
  rintro W' f ⟨W₁, g', g, hg, hg', rfl⟩
  exact hr _ g hg g' hg'

end Local

variable (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS)
  (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (T.neighbourhoodSystem.glueMapAt n))

include hAGG in
/-- **The image of `𝒜_{n+m} ⟶ 𝒜_n` eventually lies in that of `𝒪_X`**: for `X` quasi-compact,
the adic bound for `f : X' ⟶ X` (`AdicKernelBound`) gives, for all `n` large enough, an `m` such
that the image of `𝒜_{n+m} ⟶ 𝒜_n` lies in that of `𝒪_X`. -/
theorem eventually_rangeLeStructureAt_of_adicKernelBound
    (hqc : IsQuasiCompactSpace T.B T.S T.hS T.X) (hadic : T.AdicKernelBound) :
    ∃ n₁, ∀ n, n₁ ≤ n → ∃ m, T.neighbourhoodSystem.RangeLeStructureAt D n m := by
  obtain ⟨c, hc⟩ := hadic
  obtain ⟨n₀, hn₀⟩ := T.eventually_modificationKernel_inf_neighbourhoodIdeal_eq_bot hqc
  refine ⟨n₀, fun n hn => ⟨c, T.rangeLeStructureAt_of_kernelBound hAGG D c hc n ?_⟩⟩
  have hbot := hn₀ n hn
  rw [← T.kernelIdealSheaf_neighbourhoodSystem_toTarget n] at hbot
  exact T.neighbourhoodSystem.injective_algebraMap_stage D n hbot

include hAGG in
/-- **Stacks 0AGK, from the conclusion of Stacks 0AGG and the adic bound.** For `X`
quasi-compact and any choice of coequalizers `X_n` along the infinitesimal neighbourhoods `Z_n`
of `Z`, the adic bound for `f : X' ⟶ X` gives, for all `n` large enough, an `m` such that
`X_n ⟶ X_{n+m}` factors through a closed immersion `X ⟶ X_{n+m}`, a section of
`X_{n+m} ⟶ X`. -/
theorem exists_factorsThroughSection_of_adicKernelBound
    (hqc : IsQuasiCompactSpace T.B T.S T.hS T.X) (hadic : T.AdicKernelBound) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∃ m, T.neighbourhoodSystem.FactorsThroughSection D n m :=
  T.exists_factorsThroughSection_of_eventually_rangeLe hAGG hqc D
    (T.eventually_rangeLeStructureAt_of_adicKernelBound hAGG D hqc hadic)

end CoequalizerGlueSituation

end AlgebraicGeometry.Space

end
