module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.CoherentUniformBound
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.BoxSingle
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.DerivedEquivalenceKernel
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualCanonicalPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatHomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace

/-!
# No negative `Ext` between derived external products

Let `k` be a field, `X` a proper smooth `k`-scheme and `Y` a `k`-scheme. For finite locally free
`𝒪_X`-modules `ℰ`, `ℰ'` and objects `B`, `B'` of `D(𝒪_Y)` with `B'` quasi-coherent, if
`Hom(B[s], B') = 0` for all `s > 0`, then

`Hom((ℰ ⊠ B)[t], ℰ' ⊠ B') = 0` for all `t > 0`,

where `ℰ ⊠ B = L pr_1^*ℰ ⊗^𝐋 L pr_2^*B` on `X ×_k Y`. This is the vanishing
`Ext^q(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ)) = 0` for `q < 0` of [Stacks, Section 0G07], which makes the
Postnikov systems of the complexes there exist and be unique.

The source reads it off the Künneth formula for `Ext` ([Stacks, Tag 0FXZ]). Here the computation
is done directly: moving the perfect factor `V = L pr_1^*ℰ` across the tensor product with its
dual ([Stacks, Tag 0FPC]), `V^∨ = L pr_1^*(ℰ^∨)`, the adjunction `L pr_2^* ⊣ R pr_{2,*}` and the
integral transform of a derived external product
(`AlgebraicGeometry.isIso_boxTransformMap`) give

`Hom((ℰ ⊠ B)[t], ℰ' ⊠ B') = Hom(B[t], L g^*W ⊗^𝐋 B')`, `W = Rf_*(ℰ^∨ ⊗^𝐋 ℰ')`,

and `W ∈ D(𝒪_{Spec k})` is a finite sum of shifts `𝒪[-p]` with `p ≥ 0`, so the right side is a
retract of a finite sum of groups `Hom(B[t + p], B') = 0`.

## Main results

* `AlgebraicGeometry.subsingleton_hom_of_shiftSums`: `Hom(A, -)` vanishes on
  `smd(add(B[a, b]))` when `Hom(A[p], B)` vanishes for `p ∈ [a, b]`.
* `AlgebraicGeometry.hom_shift_derivedBox_eq_zero`: the vanishing above.

## References

* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.RingedSite Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Vanishing on a closure of shifts -/

section Closure

variable {C : Type*} [Category C] (A : C)

/-- The objects `Z` with `Hom(A, Z)` a subsingleton. -/
def subsingletonHomProp : ObjectProperty C := fun Z => Subsingleton (A ⟶ Z)

/-- `subsingletonHomProp A` is closed under isomorphisms. -/
instance : (subsingletonHomProp A).IsClosedUnderIsomorphisms where
  of_iso e h := @Equiv.subsingleton _ _ (Iso.homCongr (Iso.refl A) e).symm h

/-- `subsingletonHomProp A` is stable under retracts. -/
instance : (subsingletonHomProp A).IsStableUnderRetracts where
  of_retract h hY := by
    have : Subsingleton (A ⟶ _) := hY
    refine ⟨fun f g => ?_⟩
    calc f = (f ≫ h.i) ≫ h.r := by simp
      _ = (g ≫ h.i) ≫ h.r := by rw [Subsingleton.elim (f ≫ h.i) (g ≫ h.i)]
      _ = g := by simp

/-- `subsingletonHomProp A` is closed under limits of shape `J`. -/
instance (J : Type*) [Category J] : (subsingletonHomProp A).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨h⟩
    have : ∀ j, Subsingleton (A ⟶ h.diag.obj j) := h.prop_diag_obj
    exact ⟨fun f g => h.isLimit.hom_ext fun j => Subsingleton.elim _ _⟩

/-- A hom-set is a subsingleton if the hom-set between isomorphic objects is. -/
private theorem subsingleton_hom_of_iso {X X' Y Y' : C} (e : X ≅ X') (e' : Y ≅ Y')
    (h : Subsingleton (X' ⟶ Y')) : Subsingleton (X ⟶ Y) :=
  (Iso.homCongr e e').subsingleton

variable [HasShift C ℤ]

/-- **`Hom(A, -)` vanishes on `smd(add(B[a, b]))` when every `Hom(A[p], B)`, `p ∈ [a, b]`,
vanishes.** -/
theorem subsingleton_hom_of_shiftSums (B : C) (a b : ℤ)
    (h : ∀ p : ℤ, a ≤ p → p ≤ b → Subsingleton (A⟦p⟧ ⟶ B)) {Z : C}
    (hZ : shiftSums B a b Z) : Subsingleton (A ⟶ Z) := by
  refine ((ObjectProperty.retractClosure_le_iff (P := _) (subsingletonHomProp A)).2
    (ObjectProperty.limitsClosure_le ?_)) Z hZ
  refine iSup₂_le fun p hp Z' hZ' => ?_
  obtain ⟨Y, hY, ⟨e⟩⟩ := hZ'
  obtain rfl := (ObjectProperty.singleton_iff _ _).1 hY
  have := h p hp.1 hp.2
  have : Subsingleton (A⟦p⟧ ⟶ Z'⟦p⟧) := subsingleton_hom_of_iso (Iso.refl _) e ‹_›
  exact ⟨fun f g => (shiftFunctor C p).map_injective (Subsingleton.elim _ _)⟩

end Closure

/-! ### The vanishing -/

section Vanishing

attribute [local instance] CategoryTheory.Functor.flip_obj_additive
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

open Stacks.Cohomology.PerfectComplexes (IsPerfect)

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

/-- The derived dual of a module placed in degree zero lies in degrees `≥ 0`. -/
theorem isGE_derivedDual_single (E : X.Modules) :
    (Stacks.SheafOfModules.derivedDual X.toRingedSpace.sheaf
      ((DerivedCategory.singleFunctor X.Modules 0).obj E)).IsGE 0 := by
  have h := Stacks.SheafOfModules.isGE_derivedSheafHom X.toRingedSpace.sheaf
    ((DerivedCategory.singleFunctor X.Modules 0).obj E)
    (AlgebraicGeometry.RingedSite.derivedStructureSheaf
      (AlgebraicGeometry.RingedSpace.ringedSite X.toRingedSpace)) 0 0
    (inferInstance : ((DerivedCategory.singleFunctor X.Modules 0).obj E).IsLE 0)
    (inferInstance : ((DerivedCategory.singleFunctor (SheafOfModules
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AlgebraicGeometry.RingedSpace.ringedSite X.toRingedSpace).O)) 0).obj
        (SheafOfModules.unit _)).IsGE 0)
  rwa [sub_self] at h

/-- A derived tensor product with a flat module in degree zero preserves `D^{≥ 0}`. -/
theorem isGE_dtenR_single_of_isFlat (K : DerivedCategory X.Modules) (hK : K.IsGE 0)
    (N : X.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.toRingedSpace.sheaf) N) :
    (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj K).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj N)).IsGE 0 := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  let L := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor X.Modules i).mapIso
    (((derivedTensorProductFunctor X.toRingedSpace.sheaf).mapIso e.symm).app _ ≪≫
      ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj _).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app N)))
  exact isZero_homology_tensor_single_of_isFlat X.toRingedSpace.sheaf L N hN i
    ((DerivedCategory.isZero_of_isGE K 0 i hi).of_iso
      (((DerivedCategory.homologyFunctorFactors X.Modules i).app L).symm ≪≫
        (DerivedCategory.homologyFunctor X.Modules i).mapIso e))

variable [IsProper f] [Smooth f]

/-- **No negative `Ext` between derived external products.** For finite locally free `ℰ`, `ℰ'` on
a proper smooth `k`-scheme `X` and objects `B`, `B'` of `D(𝒪_Y)` with `B'` quasi-coherent and
`Hom(B[s], B') = 0` for `s > 0`, every morphism `(ℰ ⊠ B)[t] ⟶ ℰ' ⊠ B'` with `t > 0` is zero. -/
theorem subsingleton_hom_shift_derivedBox (E E' : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
    (hE' : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E')
    (B B' : DerivedCategory Y.Modules) (hB' : IsQCohAll B')
    (hvan : ∀ s : ℤ, 0 < s → Subsingleton (B⟦s⟧ ⟶ B')) (t : ℤ) (ht : 0 < t) :
    Subsingleton ((derivedBox f g ((DerivedCategory.singleFunctor X.Modules 0).obj E) B)⟦t⟧ ⟶
      derivedBox f g ((DerivedCategory.singleFunctor X.Modules 0).obj E') B') := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let E₀ := (DerivedCategory.singleFunctor X.Modules 0).obj E
  let E₀' := (DerivedCategory.singleFunctor X.Modules 0).obj E'
  have hE₀ : IsPerfect (X := X.toRingedSpace) E₀ :=
    isPerfect_singleFunctor_of_isFiniteLocallyFree X E hE
  have hE₀' : IsPerfect (X := X.toRingedSpace) E₀' :=
    isPerfect_singleFunctor_of_isFiniteLocallyFree X E' hE'
  let V := (fourierMukaiPullback f g).obj E₀
  have hV : IsPerfect (X := (pullback f g).toRingedSpace) V :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E₀ hE₀
  let T' := derivedBox f g E₀' B'
  -- the dual of `E₀`
  let D := Stacks.SheafOfModules.derivedDual X.toRingedSpace.sheaf E₀
  have hDsite := Stacks.SheafOfModules.isPerfect_derivedDual X.toRingedSpace.sheaf E₀
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X.toRingedSpace E₀ hE₀)
  have hD : IsPerfect (X := X.toRingedSpace) D :=
    Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X.toRingedSpace D hDsite
  -- `W = Rf_*(ℰ^∨ ⊗ ℰ')`
  let P := ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj D).obj E₀'
  let W := (dpush f).obj P
  have hP : IsPerfect (X := X.toRingedSpace) P := isPerfect_dtenR D E₀' hD hE₀'
  have hW : IsPerfect (X := (Spec (.of k)).toRingedSpace) W :=
    isPerfect_dpush_of_perfect_of_isProper f P hP
  obtain ⟨hWcoh, -, b₀, -, hWb₀⟩ :=
    Stacks.AlgebraicGeometry.PerfectProperDirectImage.isCoherent_homology_and_bounds_of_isPerfect
      (𝟙 (Spec (.of k))) W hW
  have hP0 : P.IsGE 0 := isGE_dtenR_single_of_isFlat D (isGE_derivedDual_single E) E'
    (AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree E' hE')
  have hW0 : W.IsGE 0 :=
    Stacks.AlgebraicGeometry.ProperSupportCoherent.isGE_derivedPushforward f P 0 hP0
  let b := max b₀ 0
  have hb : 0 ≤ b := le_max_right _ _
  have hWb : W.IsLE b := DerivedCategory.TStructure.t.isLE_of_le W b₀ b (le_max_left _ _)
  have hWsums : specFieldSums k 0 b W := specFieldSums_of_isGE_of_isLE W 0 b hb hWcoh
  -- the final group vanishes
  have hfin : Subsingleton (B⟦t⟧ ⟶ (pullbackTwist g B').obj W) :=
    subsingleton_hom_of_shiftSums (B⟦t⟧) B' 0 b (fun p hp _ => by
      have := hvan (t + p) (by omega)
      exact subsingleton_hom_of_iso ((shiftFunctorAdd' (DerivedCategory Y.Modules) t p (t + p)
        rfl).app B).symm (Iso.refl B') ‹_›) (pullbackTwist_mem_shiftSums g B' hWsums)
  -- the chain of identifications
  have h₁ := isIso_boxTransformMap f g D E₀' B' (isQCohAll_of_isPerfect hD)
    (isQCohAll_of_isPerfect hE₀') hB'
  have h₂ : Subsingleton (B⟦t⟧ ⟶ (kernelIntegralTransform f g D).obj T') :=
    subsingleton_hom_of_iso (Iso.refl _) (asIso (boxTransformMap f g D E₀' B')).symm hfin
  have h₃ : Subsingleton ((dpull (pullback.snd f g)).obj (B⟦t⟧) ⟶
      ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj
        ((fourierMukaiPullback f g).obj D)).obj T') :=
    @Equiv.subsingleton _ _
      ((derivedAdjunction (pullback.snd f g).toLRSHom.toShHom).homEquiv _ _) h₂
  have hVsite := Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect
    (pullback f g).toRingedSpace V hV
  have eD : (fourierMukaiPullback f g).obj D ≅
      Stacks.SheafOfModules.derivedDual (pullback f g).toRingedSpace.sheaf V :=
    Stacks.SheafOfModules.derivedPullbackDerivedDualIso (pullback.fst f g).toLRSHom.toShHom E₀
      (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X.toRingedSpace E₀ hE₀)
      hVsite
  have h₄ : Subsingleton ((dpull (pullback.snd f g)).obj (B⟦t⟧) ⟶
      ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj
        (Stacks.SheafOfModules.derivedDual (pullback f g).toRingedSpace.sheaf V)).obj T') :=
    subsingleton_hom_of_iso (Iso.refl _)
      (((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).mapIso eD).app T').symm h₃
  have h₅ : Subsingleton (((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj
      V).obj ((dpull (pullback.snd f g)).obj (B⟦t⟧)) ⟶ T') :=
    @Equiv.subsingleton _ _ (Stacks.SheafOfModules.derivedTensorLeftHomEquiv
      (pullback f g).toRingedSpace.sheaf V hVsite _ _) h₄
  let := (canonicalDerivedTensorProduct (pullback f g).toRingedSpace.sheaf).commShift_right V
  let e : (derivedBox f g E₀ B)⟦t⟧ ≅
      ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj V).obj
        ((dpull (pullback.snd f g)).obj (B⟦t⟧)) :=
    (((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj V).commShiftIso
        t).symm.app _ ≪≫
      ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj V).mapIso
        (((dpull (pullback.snd f g)).commShiftIso t).symm.app B)
  exact subsingleton_hom_of_iso e (Iso.refl T') h₅

end Vanishing

end AlgebraicGeometry
