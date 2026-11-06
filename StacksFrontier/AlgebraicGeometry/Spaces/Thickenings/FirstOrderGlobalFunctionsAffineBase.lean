module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.ChartLevels
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.ColimitAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderGlobalFunctionsAffineBase.ChartFunctionsDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderGlobalFunctionsAffineBase.SchemeNerveCorrection

/-!
# Regular functions extend over a first-order thickening of an affine base change

Let `U` be an algebraic space over `S` with a morphism `π : U ⟶ h_T` to a represented object of
the big fppf site, let `k : T₀ ⟶ T` be a first-order thickening, and suppose the base change
`U₀ = U ×_T T₀` is an **affine** algebraic space.  Then every global regular function on `U₀` is
the restriction of a global regular function on `U`:

`Γ(U, 𝒪_U) → Γ(U₀, 𝒪_{U₀})` is surjective.

Neither `U` nor `T` is assumed affine.

## The argument

The space `U` is quasi-compact, because `|U₀| → |U|` is surjective and `U₀` is affine, so `U` has
a single affine étale chart `w : h_W ⟶ U` that is surjective.  Its kernel pair `R = W ×_U W` and
the triple product `R₃ = W ×_U R` are schemes, and their base changes along `k` form the Čech
nerve of the affine étale covering `W₀ = W ×_T T₀ ⟶ U₀` of the affine scheme `U₀`.  A regular
function `a₀` on `U₀` restricts to `W₀`; lift it to `W`, along the closed immersion `W₀ ⟶ W` of an
affine scheme.  The defect of the lift on `R` is a Čech cocycle with values in the square-zero
ideal of `W₀ ⊆ W`, and it is a coboundary by faithfully flat descent along `W₀ ⟶ U₀`:
`AlgebraicGeometry.Space.FirstOrderGlobalFunctions.exists_sub_appTop_eq_of_isPullback`.  The
corrected lift is invariant under the kernel pair, so it descends to a compatible family on all
scheme charts of `U`
(`AlgebraicGeometry.Space.FirstOrderGlobalFunctions.exists_chartFunctions_of_kernelPair`), which
is a global regular function on `U` restricting to `a₀`.

## Main results

* `AlgebraicGeometry.Space.FirstOrderGlobalFunctions.isPullback_levelMap` and
  `AlgebraicGeometry.Space.FirstOrderGlobalFunctions.isPullback_level`: base change along
  `T₀ ⟶ T` of a morphism of charts over `U` and of a cartesian square of charts over `U`.
* `AlgebraicGeometry.Space.surjective_globalFunctionsMap_pullback_of_isFirstOrderThickening`:
  if `U ×_T T₀` is affine, then `Γ(U, 𝒪_U) → Γ(U ×_T T₀, 𝒪)` is surjective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace FirstOrderGlobalFunctions

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T T₀ : BigFppfOver B S hS} (π : U ⟶ yoneda.obj T)
  (k : T₀ ⟶ T)

/-! ### Base change of charts along `T₀ ⟶ T` -/

/-- For a morphism of charts `a : V ⟶ V'` over `U`, the morphism `levelChartBase π v` is `a`
followed by `levelChartBase π v'`. -/
theorem levelChartBase_eq {V V' : BigFppfOver B S hS} {v : yoneda.obj V ⟶ U}
    {v' : yoneda.obj V' ⟶ U} (a : V ⟶ V') (ha : yoneda.map a ≫ v' = v) :
    levelChartBase π v = a ≫ levelChartBase π v' :=
  yoneda.map_injective (by simp [← ha])

/-- The base change `V ×_T T₀ ⟶ V' ×_T T₀` of a morphism of charts `a : V ⟶ V'` over `U`. -/
def levelMap {V V' : BigFppfOver B S hS} {v : yoneda.obj V ⟶ U} {v' : yoneda.obj V' ⟶ U}
    (a : V ⟶ V') (ha : yoneda.map a ≫ v' = v) : levelChart π v k ⟶ levelChart π v' k :=
  pullback.map _ _ _ _ a (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, levelChartBase_eq π a ha]) (by simp)

variable {V V' : BigFppfOver B S hS} {v : yoneda.obj V ⟶ U} {v' : yoneda.obj V' ⟶ U}

/-- The morphism `levelMap π k a ha` lies over `a : V ⟶ V'` under the first projections. -/
@[reassoc]
theorem levelMap_fst (a : V ⟶ V') (ha : yoneda.map a ≫ v' = v) :
    levelMap π k a ha ≫ pullback.fst _ _ = pullback.fst _ _ ≫ a :=
  pullback.lift_fst _ _ _

/-- The morphism `levelMap π k a ha` commutes with the second projections to `T₀`. -/
@[reassoc]
theorem levelMap_snd (a : V ⟶ V') (ha : yoneda.map a ≫ v' = v) :
    levelMap π k a ha ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [levelMap, pullback.lift_snd, Category.comp_id]

/-- The morphism `levelMap π k a ha` commutes with the maps `levelChartMap` to `U ×_T T₀`. -/
theorem levelMap_levelChartMap (a : V ⟶ V') (ha : yoneda.map a ≫ v' = v) :
    yoneda.map (levelMap π k a ha) ≫ levelChartMap π v' k = levelChartMap π v k := by
  apply pullback.hom_ext
  · rw [Category.assoc, levelChartMap_fst, levelChartMap_fst, ← Functor.map_comp_assoc,
      levelMap_fst, Functor.map_comp, Category.assoc, ha]
  · rw [Category.assoc, levelChartMap_snd, levelChartMap_snd, ← Functor.map_comp, levelMap_snd]

/-- `V ×_T T₀` is the base change of `V' ×_T T₀` along a morphism `a : V ⟶ V'` of charts. -/
theorem isPullback_levelMap (a : V ⟶ V') (ha : yoneda.map a ≫ v' = v) :
    IsPullback (pullback.fst (levelChartBase π v) k) (levelMap π k a ha) a
      (pullback.fst (levelChartBase π v') k) := by
  have hout' : IsPullback (levelMap π k a ha ≫ pullback.snd _ _)
      (pullback.fst (levelChartBase π v) k) k (a ≫ levelChartBase π v') := by
    rw [levelMap_snd, ← levelChartBase_eq π a ha]
    exact (IsPullback.of_hasPullback (levelChartBase π v) k).flip
  exact (IsPullback.of_right hout' (levelMap_fst π k a ha)
    (IsPullback.of_hasPullback (levelChartBase π v') k).flip).flip

/-- **The base change of a cartesian square of charts over `U` is cartesian over `U ×_T T₀`.** -/
theorem isPullback_level {P : BigFppfOver B S hS} {a : P ⟶ V} {b : P ⟶ V'}
    (hP : IsPullback (yoneda.map a) (yoneda.map b) v v') :
    IsPullback (yoneda.map (levelMap π k a (v := yoneda.map a ≫ v) rfl))
      (yoneda.map (levelMap π k b hP.w.symm)) (levelChartMap π v k) (levelChartMap π v' k) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_levelChart π v k)
  · rw [← Functor.map_comp, levelMap_fst, Functor.map_comp, levelChartMap_fst]
    exact ((isPullback_levelMap π k b hP.w.symm).map yoneda).paste_horiz hP
  · rw [levelMap_levelChartMap, levelMap_levelChartMap]

/-! ### Surjectivity, chart properties and the corrected lift -/

/-- The base change `U ×_T T₀ ⟶ U` of a first-order thickening `k : T₀ ⟶ T` is surjective. -/
theorem isSurjective_pullback_fst_of_isFirstOrderThickening
    (hk : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map k)) :
    IsSurjective B S hS (pullback.fst π (yoneda.map k)) := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  exact isSurjective_of_presheafSurjective B S hS _
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback π (yoneda.map k)).flip
      ((MorphismProperty.relative_map_iff (F := yoneda)
        (P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))).2 ⟨hk.isThickening.2⟩))

/-- A morphism `ρ : W ×_T T₀ ⟶ X₀` to a represented model `X₀` of `U ×_T T₀` has every
base-change-stable property of the chart `w : h_W ⟶ U`. -/
theorem property_map_of_levelChartMap {W X₀ : BigFppfOver B S hS} {w : yoneda.obj W ⟶ U}
    (e : pullback π (yoneda.map k) ≅ yoneda.obj X₀) {ρ : levelChart π w k ⟶ X₀}
    (hρ : yoneda.map ρ = levelChartMap π w k ≫ e.hom) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    (hw : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf w) :
    P ((BigFppfOver.toScheme B S hS).map ρ) := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))
  refine (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))).1 ?_
  rw [hρ]
  exact MorphismProperty.RespectsIso.postcomp _ e.hom _
    (MorphismProperty.of_isPullback (isPullback_levelChart π w k) hw)

/-- The two face maps `R₃ ⟶ R` of the triple product `R₃ = W ×_U R` of a kernel pair
`s, t : R ⟶ W` of `w`. -/
theorem exists_kernelPair_faces {W R R₃ : BigFppfOver B S hS} {w : yoneda.obj W ⟶ U}
    {s t : R ⟶ W} {q : R₃ ⟶ W} {d₀ : R₃ ⟶ R} (hR : IsPullback (yoneda.map s) (yoneda.map t) w w)
    (hq : yoneda.map q ≫ w = yoneda.map d₀ ≫ yoneda.map s ≫ w) :
    ∃ d₁ d₂ : R₃ ⟶ R, d₁ ≫ s = q ∧ d₁ ≫ t = d₀ ≫ t ∧ d₂ ≫ s = q ∧ d₂ ≫ t = d₀ ≫ s := by
  have hw₁ : yoneda.map q ≫ w = yoneda.map (d₀ ≫ t) ≫ w := by
    rw [hq, Functor.map_comp, Category.assoc]
    exact yoneda.map d₀ ≫= hR.w
  have hw₂ : yoneda.map q ≫ w = yoneda.map (d₀ ≫ s) ≫ w := by
    rw [hq, Functor.map_comp, Category.assoc]
  obtain ⟨d₁, hd₁⟩ := yoneda.map_surjective (hR.lift (yoneda.map q) (yoneda.map (d₀ ≫ t)) hw₁)
  obtain ⟨d₂, hd₂⟩ := yoneda.map_surjective (hR.lift (yoneda.map q) (yoneda.map (d₀ ≫ s)) hw₂)
  exact ⟨d₁, d₂, yoneda.map_injective (by rw [Functor.map_comp, hd₁, hR.lift_fst]),
    yoneda.map_injective (by rw [Functor.map_comp, hd₁, hR.lift_snd]),
    yoneda.map_injective (by rw [Functor.map_comp, hd₂, hR.lift_fst]),
    yoneda.map_injective (by rw [Functor.map_comp, hd₂, hR.lift_snd])⟩

/-- The base change `W ×_T T₀ ⟶ W` of a first-order thickening `k : T₀ ⟶ T` is a first-order
thickening. -/
theorem isFirstOrderThickening_map_pullback_fst_levelChartBase
    (hk : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map k))
    {W : BigFppfOver B S hS} (w : yoneda.obj W ⟶ U) :
    Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π w) k)) := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  exact Stacks.Thickenings.isFirstOrderThickening_of_isPullback
    ((IsPullback.of_hasPullback (levelChartBase π w) k).map (BigFppfOver.toScheme B S hS)) hk

/-- **The corrected lift.**  The restriction to `W ×_T T₀` of a regular function on the affine
model `X₀` of `U ×_T T₀` lifts to a regular function on the affine chart `W` that is invariant
under the kernel pair `s, t : R ⟶ W` of `w`. -/
theorem exists_lift_of_kernelPair
    (hk : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map k))
    {W R X₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X₀)] {w : yoneda.obj W ⟶ U}
    (hwE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    {s t : R ⟶ W} (hR : IsPullback (yoneda.map s) (yoneda.map t) w w)
    (e : pullback π (yoneda.map k) ≅ yoneda.obj X₀) {ρ : levelChart π w k ⟶ X₀}
    (hρ : yoneda.map ρ = levelChartMap π w k ≫ e.hom)
    (hρS : Surjective ((BigFppfOver.toScheme B S hS).map ρ))
    (hρE : Etale ((BigFppfOver.toScheme B S hS).map ρ))
    (b : Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤)) :
    ∃ A : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤),
      ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π w) k)).appTop A =
        ((BigFppfOver.toScheme B S hS).map ρ).appTop b ∧
      ((BigFppfOver.toScheme B S hS).map s).appTop A =
        ((BigFppfOver.toScheme B S hS).map t).appTop A := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  obtain ⟨R₃, d₀, p₃, hR₃p⟩ := hwE.1 (yoneda.map s ≫ w)
  obtain ⟨q, rfl⟩ := yoneda.map_surjective p₃
  have hR₃ : IsPullback (yoneda.map q) (yoneda.map d₀) w (yoneda.map s ≫ w) := hR₃p
  obtain ⟨d₁, d₂, h₁s, h₁t, h₂s, h₂t⟩ := exists_kernelPair_faces hR hR₃.w
  have hb : yoneda.map t ≫ w = yoneda.map s ≫ w := hR.w.symm
  have hd : yoneda.map d₀ ≫ (yoneda.map s ≫ w) = yoneda.map q ≫ w := hR₃.w.symm
  have : Mono e.hom := ⟨fun g h hgh => by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (· ≫ e.inv) hgh⟩
  have hC : IsPullback (levelMap π k s (v := yoneda.map s ≫ w) rfl) (levelMap π k t hb) ρ ρ := by
    refine IsPullback.of_map_of_faithful yoneda ?_
    rw [hρ]
    exact FormalSpace.DependentProduct.isPullback_comp_mono (isPullback_level π k hR) e.hom
  have hD : IsPullback (levelMap π k q (v := yoneda.map q ≫ w) rfl) (levelMap π k d₀ hd) ρ
      (levelMap π k s (v := yoneda.map s ≫ w) rfl ≫ ρ) := by
    refine IsPullback.of_map_of_faithful yoneda ?_
    rw [Functor.map_comp, hρ, ← Category.assoc, levelMap_levelChartMap]
    exact FormalSpace.DependentProduct.isPullback_comp_mono (isPullback_level π k hR₃) e.hom
  have hd₀E : Etale ((BigFppfOver.toScheme B S hS).map d₀) :=
    (MorphismProperty.relative_map_iff (F := yoneda) (P := MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))).1
      (MorphismProperty.of_isPullback hR₃ hwE)
  have hπW := isFirstOrderThickening_map_pullback_fst_levelChartBase π k hk w
  have := hπW.1
  obtain ⟨a, ha⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π w) k))).2
    (((BigFppfOver.toScheme B S hS).map ρ).appTop b)
  obtain ⟨m, hm, hmeq⟩ := exists_sub_appTop_eq_of_isPullback hπW
    ((isPullback_levelMap π k t hb).map (BigFppfOver.toScheme B S hS))
    ((isPullback_levelMap π k d₀ hd).map (BigFppfOver.toScheme B S hS))
    (hC.map (BigFppfOver.toScheme B S hS))
    (by simpa only [Functor.map_comp] using hD.map (BigFppfOver.toScheme B S hS))
    (by rw [← Functor.map_comp, levelMap_fst, Functor.map_comp])
    (by rw [← Functor.map_comp, levelMap_fst, Functor.map_comp])
    (by rw [← Functor.map_comp, h₁s]) (by rw [← Functor.map_comp, h₂s])
    (by rw [← Functor.map_comp, ← Functor.map_comp, h₁t])
    (by rw [← Functor.map_comp, ← Functor.map_comp, h₂t])
    inferInstance inferInstance hρS a (by
      rw [ha]
      show ((BigFppfOver.toScheme B S hS).map (levelMap π k s (v := yoneda.map s ≫ w) rfl) ≫
          (BigFppfOver.toScheme B S hS).map ρ).appTop _ =
        ((BigFppfOver.toScheme B S hS).map (levelMap π k t hb) ≫
          (BigFppfOver.toScheme B S hS).map ρ).appTop _
      rw [← Functor.map_comp, ← Functor.map_comp, hC.w])
  exact ⟨a - m, by rw [map_sub, hm, sub_zero, ha], hmeq⟩

/-- Two compatible families of regular functions on the scheme charts of a presheaf `X`
isomorphic to a represented object `X₀` agree once they agree on the chart `e.inv`. -/
theorem chartFunctions_ext_of_iso {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X₀ : BigFppfOver B S hS} (e : X ≅ yoneda.obj X₀) {F G : chartFunctions B S hS X}
    (h : F.val (op (CostructuredArrow.mk e.inv)) = G.val (op (CostructuredArrow.mk e.inv))) :
    F = G := by
  refine Subtype.ext (funext fun j => ?_)
  obtain ⟨φ, hφ⟩ := yoneda.map_surjective (j.unop.hom ≫ e.hom)
  let f : j.unop ⟶ CostructuredArrow.mk e.inv := CostructuredArrow.homMk φ (by
    show yoneda.map φ ≫ e.inv = j.unop.hom
    rw [hφ, Category.assoc, e.hom_inv_id, Category.comp_id])
  have h₁ := F.property f.op
  have h₂ := G.property f.op
  change _ = F.val (op j.unop) at h₁
  change _ = G.val (op j.unop) at h₂
  rw [← h₁, ← h₂, h]

/-- A family `E` on the charts of `U` descended from a function `A` on the chart `W` restricts on
`U ×_T T₀` to `ē`, as soon as `A` and `ē` restrict to the same function on `W ×_T T₀`. -/
theorem chartFunctionsMap_eq_of_isDescent {W X₀ : BigFppfOver B S hS} {w : yoneda.obj W ⟶ U}
    (e : pullback π (yoneda.map k) ≅ yoneda.obj X₀) {ρ : levelChart π w k ⟶ X₀}
    (hρ : yoneda.map ρ = levelChartMap π w k ≫ e.hom)
    (hρS : Surjective ((BigFppfOver.toScheme B S hS).map ρ))
    (hρE : Etale ((BigFppfOver.toScheme B S hS).map ρ))
    {A : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)} {E : chartFunctions B S hS U}
    (hE : ∀ j, IsDescent (w := w) A j (E.val (op j)))
    {ē : chartFunctions B S hS (pullback π (yoneda.map k))}
    (hA : ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π w) k)).appTop A =
      ((BigFppfOver.toScheme B S hS).map ρ).appTop (ē.val (op (CostructuredArrow.mk e.inv)))) :
    chartFunctionsMap B S hS (pullback.fst π (yoneda.map k)) E = ē := by
  refine chartFunctions_ext_of_iso e ?_
  refine gamma_injective_of_etale_surjection B S hS ρ hρS hρE ?_
  have hjW : yoneda.map ρ ≫ e.inv = levelChartMap π w k := by
    rw [hρ, Category.assoc, e.hom_inv_id, Category.comp_id]
  let fW : CostructuredArrow.mk (levelChartMap π w k) ⟶ CostructuredArrow.mk e.inv :=
    CostructuredArrow.homMk ρ hjW
  have h₁ := (chartFunctionsMap B S hS (pullback.fst π (yoneda.map k)) E).property fW.op
  have h₂ := ē.property fW.op
  change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ρ).op).hom _ = _ at h₁ h₂
  rw [h₁, h₂]
  show E.val (op (CostructuredArrow.mk (levelChartMap π w k ≫ pullback.fst π (yoneda.map k))))
    = _
  have hdesc := hE (CostructuredArrow.mk (levelChartMap π w k ≫ pullback.fst π (yoneda.map k)))
    (𝟙 _) (pullback.fst (levelChartBase π w) k) (by
      rw [CategoryTheory.Functor.map_id, Category.id_comp, CostructuredArrow.mk_hom_eq_self,
        levelChartMap_fst])
  rw [CategoryTheory.Functor.map_id] at hdesc
  change E.val _ = _ at hdesc
  rw [hdesc]
  show ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π w) k)).appTop A = _
  rw [hA]
  exact h₂

end FirstOrderGlobalFunctions

open FirstOrderGlobalFunctions

/-- **Regular functions extend over a first-order thickening of an affine base change.**  Let `U`
be an algebraic space with a morphism `π : U ⟶ h_T`, let `k : T₀ ⟶ T` be a first-order thickening
and suppose `U ×_T T₀` is affine.  Then pullback of global regular functions along the projection
`U ×_T T₀ ⟶ U` is surjective. -/
theorem surjective_globalFunctionsMap_pullback_of_isFirstOrderThickening
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    {T₀ T : BigFppfOver B S hS} (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map k))
    (π : U ⟶ yoneda.obj T) (hU₀ : IsAffineSpace B S hS (pullback π (yoneda.map k))) :
    Function.Surjective (globalFunctionsMap B S hS
      (V := ⟨pullback π (yoneda.map k), IsAffineSpace.isAlgebraicSpace hU₀⟩)
      (U := ⟨U, hU⟩) (ObjectProperty.homMk (pullback.fst π (yoneda.map k)))) := by
  intro ā
  obtain ⟨X₀, hX₀, ⟨e⟩⟩ := id hU₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj X₀) := hX₀
  have hcpt : IsCompact (Set.univ : Set (points B S hS U)) := by
    have : CompactSpace (points B S hS (pullback π (yoneda.map k))) :=
      (isQuasiCompactSpace_iff_compactSpace_points B S hS _
        (IsAffineSpace.isAlgebraicSpace hU₀)).1 (IsAffineSpace.isQuasiCompactSpace hU₀)
    rw [← Set.image_univ_of_surjective
      (isSurjective_pullback_fst_of_isFirstOrderThickening π k hk)]
    exact isCompact_univ.image (continuous_pointsMap B S hS _)
  obtain ⟨W, w, hW, hwE, hwrange⟩ := exists_affine_etale_chart_of_isCompact B S hS U hU hcpt
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hW
  have hwS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS U hU W w).2
      fun x => hwrange (Set.mem_univ x)
  obtain ⟨R, t, p, hRp⟩ := hwE.1 w
  obtain ⟨s, rfl⟩ := yoneda.map_surjective p
  have hR : IsPullback (yoneda.map s) (yoneda.map t) w w := hRp
  obtain ⟨ρ, hρ⟩ := yoneda.map_surjective (levelChartMap π w k ≫ e.hom)
  have hρE : Etale ((BigFppfOver.toScheme B S hS).map ρ) :=
    property_map_of_levelChartMap π k e hρ _ hwE
  have hρS : Surjective ((BigFppfOver.toScheme B S hS).map ρ) :=
    property_map_of_levelChartMap π k e hρ _ hwS
  obtain ⟨A, hA, hAst⟩ := exists_lift_of_kernelPair π k hk hwE hR e hρ hρS hρE
    (((globalFunctionsChartEquiv B S hS
      ⟨pullback π (yoneda.map k), IsAffineSpace.isAlgebraicSpace hU₀⟩).val ā).val
        (op (CostructuredArrow.mk e.inv)))
  obtain ⟨E, hE⟩ := exists_chartFunctions_of_kernelPair hwE hwS hR A hAst
  refine ⟨chartFunctionsToSmall B S hS U E, ?_⟩
  apply (globalFunctionsChartEquiv B S hS _).val.injective
  rw [globalFunctionsMap_chart]
  have hEU : (globalFunctionsChartEquiv B S hS ⟨U, hU⟩).val (chartFunctionsToSmall B S hS U E) =
      E :=
    chartFunctionsToSmall_injective B S hS U hU
      ((globalFunctionsChartEquiv B S hS ⟨U, hU⟩).property _)
  rw [hEU]
  exact chartFunctionsMap_eq_of_isDescent π k e hρ hρS hρE hE hA

end AlgebraicGeometry.Space

end
