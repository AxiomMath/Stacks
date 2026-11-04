module

public import StacksFrontier.AlgebraicGeometry.Properties.RelativeAmpleExternalTensorProduct
public import StacksFrontier.AlgebraicGeometry.Quot.GraphOfRelativeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeModuleInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageTensorInvertible
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeRepresentation

/-!
# The module `pr₁^* 𝒩 ⊗ pr₂^* ℒ` on `Z ×_Q X` is relatively ample

Let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces over a scheme `S` of a big fppf
site, `𝒩` an invertible `𝒪_Z`-module ample relative to `z` and `ℒ` an invertible `𝒪_X`-module
ample relative to `x` (Stacks 0D31). The module `ℳ = pr₁^* 𝒩 ⊗ pr₂^* ℒ` on the ambient space
`Z ×_Q X` of the graph construction is invertible and ample relative to `Z ×_Q X ⟶ Q`. This is the
module of Stacks 0DPR, and these are the two facts about it that the proof of 0DPR uses when it
applies Stacks 0DPI to `Hilb^{P, ℳ}_{Z ×_Q X / Q}`.

## Main definitions

* `AlgebraicGeometry.Space.graphAmbientTensor`: the module `pr₁^* 𝒩 ⊗ pr₂^* ℒ` on `Z ×_Q X`.

## Main results

* `AlgebraicGeometry.Space.isInvertible_graphAmbientTensor`: it is invertible.
* `AlgebraicGeometry.Space.isRelativelyAmple_graphAmbientTensor`: it is ample relative to
  `Z ×_Q X ⟶ Q`.

## The route

Both `z` and `x` are representable, carrying relatively ample modules (Stacks 0D34). For a scheme
`T` over `Q` and a cartesian square identifying `(Z ×_Q X) ×_Q T` with a scheme `U`, the base
changes `Z_T` and `X_T` are schemes, `U` is their fibre product over `T` (two pastings of
cartesian squares of presheaves, read on schemes because the site's forgetful functor preserves
fibre products), and the reading of `ℳ` on `U` is the external tensor product of the readings of
`𝒩` on `Z_T` and of `ℒ` on `X_T`: the inverse image of Stacks 03LU commutes with tensor products
(Stacks 03EL), the reading on the scheme `U` commutes with tensor products of quasi-coherent
modules, and the readings commute with base change. The scheme-level statement is Stacks 0DNK
relative to `T`, `Stacks.AmpleExternalTensor.isRelativelyAmple_tensorModules_of_isPullback`.

## References

* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
* [Stacks Project, Tag 0DNK](https://stacks.math.columbia.edu/tag/0DNK)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D34](https://stacks.math.columbia.edu/tag/0D34)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

/-- The first projection `Z ×_Q X ⟶ Z` of the ambient space of the graph construction, as a
morphism of algebraic spaces. -/
abbrev graphAmbientFst : graphAmbient B S hS z x hZ hX hQ ⟶ (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (pullback.fst z x)

/-- The second projection `Z ×_Q X ⟶ X` of the ambient space of the graph construction, as a
morphism of algebraic spaces. -/
abbrev graphAmbientSnd : graphAmbient B S hS z x hZ hX hQ ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (pullback.snd z x)

/-- **The module `ℳ = pr₁^* 𝒩 ⊗ pr₂^* ℒ` of Stacks 0DPR** on the ambient space `Z ×_Q X` of the
graph construction, for an `𝒪_Z`-module `𝒩` and an `𝒪_X`-module `ℒ`. -/
def graphAmbientTensor (N : Modules.{u, u} B S hS Z hZ) (L : Modules.{u, u} B S hS X hX) :
    Modules.{u, u} B S hS (graphAmbient B S hS z x hZ hX hQ).1
      (graphAmbient B S hS z x hZ hX hQ).2 :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (graphAmbient B S hS z x hZ hX hQ).1
        (graphAmbient B S hS z x hZ hX hQ).2).O).obj
    ((modulePullback B S hS (graphAmbientFst z x hZ hX hQ)).obj N)).obj
    ((modulePullback B S hS (graphAmbientSnd z x hZ hX hQ)).obj L)

variable {z x hZ hX hQ}
variable (N : Modules.{u, u} B S hS Z hZ) (L : Modules.{u, u} B S hS X hX)
    [hNi : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z hZ).O)).property N]
    [hLi : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).property L]

include hNi hLi in
/-- **`pr₁^* 𝒩 ⊗ pr₂^* ℒ` is invertible** when `𝒩` and `ℒ` are: inverse images of invertible
modules are invertible (Stacks 0B8P), and so is a tensor product of invertible modules
(Stacks 01CT). -/
instance isInvertible_graphAmbientTensor :
    Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (graphAmbient B S hS z x hZ hX hQ).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (graphAmbient B S hS z x hZ hX hQ).1 (graphAmbient B S hS z x hZ hX hQ).2).O)).property
      (graphAmbientTensor z x hZ hX hQ N L) := by
  have h₁ : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (graphAmbient B S hS z x hZ hX hQ).1)
      (structureRingPresheaf_isSheaf B S hS _ (graphAmbient B S hS z x hZ hX hQ).2)
      ((modulePullback B S hS (graphAmbientFst z x hZ hX hQ)).obj N) :=
    stacksIsInvertible_modulePullback_obj B S hS (graphAmbientFst z x hZ hX hQ) N
  have h₂ : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (graphAmbient B S hS z x hZ hX hQ).1)
      (structureRingPresheaf_isSheaf B S hS _ (graphAmbient B S hS z x hZ hX hQ).2)
      ((modulePullback B S hS (graphAmbientSnd z x hZ hX hQ)).obj L) :=
    stacksIsInvertible_modulePullback_obj B S hS (graphAmbientSnd z x hZ hX hQ) L
  exact Stacks.SheafOfModules.isInvertible_tensorSheaf.{u, u + 1, u}
    (structurePresheaf B S hS (graphAmbient B S hS z x hZ hX hQ).1)
    (structureRingPresheaf_isSheaf B S hS _ (graphAmbient B S hS z x hZ hX hQ).2) _ _

include hNi hLi in
/-- The reading of `pr₁^* 𝒩 ⊗ pr₂^* ℒ` on a scheme `U` over `Z ×_Q X`, along `p`, is the tensor
product of the readings of `𝒩` along `p ≫ pr₁` and of `ℒ` along `p ≫ pr₂`: the inverse image
commutes with tensor products (Stacks 03EL), and so does the reading on the scheme `U` of
quasi-coherent modules. -/
def baseChangeModuleGraphAmbientTensorIso (U : BigFppfOver B S hS)
    (p : yoneda.obj U ⟶ (graphAmbient B S hS z x hZ hX hQ).1) :
    baseChangeModule B S hS (graphAmbientTensor z x hZ hX hQ N L) U p ≅
      Stacks.RelativeVeryAmple.tensorModules _
        (baseChangeModule B S hS (X := ⟨Z, hZ⟩) N U (p ≫ pullback.fst z x))
        (baseChangeModule B S hS (X := ⟨X, hX⟩) L U (p ≫ pullback.snd z x)) :=
  let hp : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
      graphAmbient B S hS z x hZ hX hQ := ObjectProperty.homMk p
  let A := (modulePullback B S hS (graphAmbientFst z x hZ hX hQ)).obj N
  let A' := (modulePullback B S hS (graphAmbientSnd z x hZ hX hQ)).obj L
  let qA := isQuasicoherentOnSite_modulePullback_of_isInvertible hp A
    (stacksIsInvertible_modulePullback_obj B S hS (graphAmbientFst z x hZ hX hQ) N)
  let qA' := isQuasicoherentOnSite_modulePullback_of_isInvertible hp A'
    (stacksIsInvertible_modulePullback_obj B S hS (graphAmbientSnd z x hZ hX hQ) L)
  (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U)).mapIso
      ((modulePullback B S hS hp).mapIso (modulesTensorObjIso B S hS _ _ A A').symm ≪≫
        modulePullbackTensorIso B S hS hp A A') ≪≫
    restrictToChartSchemeIdEtaleChartTensorIso B S hS U _ _ qA qA' ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).mapIso
        (baseChangeModuleCompIso B S hS (graphAmbientFst z x hZ hX hQ) N U p).symm).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).obj _).mapIso
        (baseChangeModuleCompIso B S hS (graphAmbientSnd z x hZ hX hQ) L U p).symm

/-- A map `u` from a representable presheaf with `u ≫ z = yoneda.map q ≫ g`, for `z` relatively
representable, factors through the base change `hz.pullback g`, compatibly with both projections. -/
private theorem exists_yoneda_lift {C : Type*} [Category.{u} C] {Z Q : Cᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    (hz : yoneda.relativelyRepresentable z) {T U : C} (g : yoneda.obj T ⟶ Q) (q : U ⟶ T)
    (u : yoneda.obj U ⟶ Z) (w : u ≫ z = yoneda.map q ≫ g) :
    ∃ a : U ⟶ hz.pullback g, yoneda.map a ≫ hz.fst g = u ∧
      yoneda.map a ≫ yoneda.map (hz.snd g) = yoneda.map q :=
  ⟨yoneda.preimage (hz.isPullback g |>.lift _ _ w), by simp, by simp⟩

include hNi hLi in
/-- **`pr₁^* 𝒩 ⊗ pr₂^* ℒ` is ample relative to `Z ×_Q X ⟶ Q`** (Stacks 0D31) when `𝒩` is
ample relative to `z : Z ⟶ Q` and `ℒ` relative to `x : X ⟶ Q`. This is the input on `ℳ` that
the proof of Stacks 0DPR needs to apply Stacks 0DPI to `Z ×_Q X ⟶ Q`.

On a scheme base change `U = (Z ×_Q X) ×_Q T` it is Stacks 0DNK relative to `T`
(`Stacks.AmpleExternalTensor.isRelativelyAmple_tensorModules_of_isPullback`) for
`U = Z_T ×_T X_T`, the reading of `ℳ` on `U` being the external tensor product of the readings
of `𝒩` on `Z_T` and of `ℒ` on `X_T`. -/
theorem isRelativelyAmple_graphAmbientTensor
    (hN : IsRelativelyAmple B S hS
      (ObjectProperty.homMk z : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩) N)
    (hL : IsRelativelyAmple B S hS
      (ObjectProperty.homMk x : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩) L) :
    IsRelativelyAmple B S hS (graphAmbientMap B S hS z x hZ hX hQ)
      (graphAmbientTensor z x hZ hX hQ N L) := by
  have hzr : yoneda.relativelyRepresentable z := hN.1
  have hxr : yoneda.relativelyRepresentable x := hL.1
  refine ⟨MorphismProperty.comp_mem _ _ _
    (MorphismProperty.pullback_fst z x hxr) hzr, fun T U g p q hsq => ?_⟩
  have hsq' : IsPullback p (yoneda.map q) (pullback.fst z x ≫ z) g := hsq
  -- the base changes `Z_T` and `X_T`, and the two maps `U ⟶ Z_T`, `U ⟶ X_T`
  have hZsq := hzr.isPullback g
  have hXsq := hxr.isPullback g
  have wa : (p ≫ pullback.fst z x) ≫ z = yoneda.map q ≫ g := by
    rw [Category.assoc]; exact hsq'.w
  have wb : (p ≫ pullback.snd z x) ≫ x = yoneda.map q ≫ g := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact wa
  obtain ⟨a, ha₁, ha₂⟩ := exists_yoneda_lift hzr g q _ wa
  obtain ⟨b, hb₁, hb₂⟩ := exists_yoneda_lift hxr g q _ wb
  -- `U = Z_T ×_T X_T`, first for the represented presheaves, then for the schemes
  have h₁ : IsPullback p (yoneda.map a) (pullback.fst z x) (hzr.fst g) :=
    IsPullback.of_bot (by rw [ha₂]; exact hsq') ha₁.symm hZsq
  have h₂ : IsPullback (p ≫ pullback.snd z x) (yoneda.map a) x (hzr.fst g ≫ z) :=
    h₁.paste_horiz (IsPullback.of_hasPullback z x).flip
  have h₃ : IsPullback (yoneda.map b) (yoneda.map a) (yoneda.map (hxr.snd g))
      (yoneda.map (hzr.snd g)) := by
    refine IsPullback.of_right ?_ (hb₂.trans ha₂.symm) hXsq
    rw [hb₁, ← hZsq.w]
    exact h₂
  have hU := Stack.ChartBaseChange.isPullback_toScheme_of_isPullback_yoneda h₃.flip
  have haq : a ≫ hzr.snd g = q := yoneda.map_injective (by rw [Functor.map_comp, ha₂])
  -- the scheme-level statement: Stacks 0DNK relative to `T`
  obtain ⟨hNT, hNamp⟩ := hN.2 T (hzr.pullback g) g (hzr.fst g) (hzr.snd g) hZsq
  obtain ⟨hLT, hLamp⟩ := hL.2 T (hxr.pullback g) g (hxr.fst g) (hxr.snd g) hXsq
  have key := Stacks.AmpleExternalTensor.isRelativelyAmple_tensorModules_of_isPullback _ _ _ _
    hU hNamp hLamp
  rw [← Functor.map_comp, haq] at key
  -- the reading of `ℳ` on `U` is the external tensor product of the readings
  obtain ⟨eN⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible
    (X := ⟨Z, hZ⟩) N hNi (hzr.pullback g) U (hzr.fst g) a
  obtain ⟨eL⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible
    (X := ⟨X, hX⟩) L hLi (hxr.pullback g) U (hxr.fst g) b
  rw [ha₁] at eN
  rw [hb₁] at eL
  have := hNT
  have := hLT
  have hinv := isInvertibleModule_baseChangeModule _
    (isInvertible_graphAmbientTensor (z := z) (x := x) (hQ := hQ) N L) U p
  exact ⟨hinv, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _
    (baseChangeModuleGraphAmbientTensorIso N L U p ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso _ eN eL)).mpr key⟩

end AlgebraicGeometry.Space

end
