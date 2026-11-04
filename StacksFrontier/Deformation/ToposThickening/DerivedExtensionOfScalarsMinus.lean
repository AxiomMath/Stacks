module

public import StacksFrontier.Deformation.ToposThickening.DerivedReductionData

/-!
# Derived base change preserves bounded above objects

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site. Derived base change
`- ⊗^L_O O₀ : D(O) ⥤ D(O₀)` carries `D^{≤ n}(O)` into `D^{≤ n}(O₀)` for every `n`, hence
`D⁻(O)` into `D⁻(O₀)`. This is the claim "`K₀ = K ⊗^L_O O₀` in `D⁻(O₀)`" of Stacks 0DIY and 0DIZ.

The proof is the adjunction: derived base change is left adjoint to restriction of scalars on
derived categories (`Deformation.ComplexLift.derivedAdjunctionOf`), and restriction of scalars,
being exact, carries `D^{≥ n+1}(O₀)` into `D^{≥ n+1}(O)`; so for `K ∈ D^{≤ n}(O)` and
`Y ∈ D^{≥ n+1}(O₀)` every morphism `K ⊗^L_O O₀ ⟶ Y` is adjoint to a morphism `K ⟶ Y|_O`, which
vanishes, and an object with no nonzero morphism to `D^{≥ n+1}` lies in `D^{≤ n}`.

## Main results

* `Deformation.ComplexLift.isGE_restrictionOnDerived_obj`: restriction of scalars on derived
  categories preserves `D^{≥ n}`.
* `Deformation.ComplexLift.DerivedExtensionOfScalars.isLE_baseChange_obj`: derived base change
  preserves `D^{≤ n}`.
* `Deformation.ComplexLift.DerivedExtensionOfScalars.baseChangeMinus`: derived base change as a
  functor `D⁻(O) ⥤ D⁻(O₀)`.

## References

* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Restriction of scalars preserves `D^{≥ n}`.** An object of `D^{≥ n}(O₀)` is represented by
a complex vanishing in degrees `< n`, and restriction of scalars, which needs no deriving, is
computed on it degreewise. -/
theorem isGE_restrictionOnDerived_obj
    (Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))
    (n : ℤ) [Y.IsGE n] : ((restrictionOnDerived.{d, d₀} f).obj Y).IsGE n := by
  obtain ⟨K, hK, ⟨e⟩⟩ := Y.exists_iso_Q_obj_of_isGE n
  let F := SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)
  have hFK : CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      n := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact F.map_isZero (K.isZero_of_isStrictlyGE n i hi)
  have : DerivedCategory.TStructure.t.IsGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj K) n :=
    (inferInstance :
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).IsGE n)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((restrictionOnDerived.{d, d₀} f).mapIso e ≪≫ F.mapDerivedCategoryFactors.app K).symm n

namespace DerivedExtensionOfScalars

variable {f} (T : DerivedExtensionOfScalars.{d, d₀} f)

/-- **Derived base change preserves `D^{≤ n}`.** For `K ∈ D^{≤ n}(O)` and `Y ∈ D^{≥ n+1}(O₀)` a
morphism `K ⊗^L_O O₀ ⟶ Y` is adjoint to a morphism `K ⟶ Y|_O` into `D^{≥ n+1}(O)`, which
vanishes. -/
theorem isLE_baseChange_obj
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (n : ℤ) [K.IsLE n] : (T.baseChange.obj K).IsLE n := by
  rw [DerivedCategory.IsLE, DerivedCategory.TStructure.t.isLE_iff_orthogonal n (n + 1) rfl]
  intro Y g hY
  have := isGE_restrictionOnDerived_obj.{d, d₀} f Y (n + 1)
  have : T.baseChange.IsLeftAdjoint := (derivedAdjunctionOf.{d, d₀} f T).isLeftAdjoint
  have h0 : (derivedAdjunctionOf.{d, d₀} f T).homEquiv K Y g = 0 :=
    DerivedCategory.TStructure.t.zero _ n (n + 1)
  rw [← ((derivedAdjunctionOf.{d, d₀} f T).homEquiv K Y).symm_apply_apply g, h0,
    Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]

/-- Derived base change carries bounded above objects to bounded above objects. -/
theorem minus_baseChange_obj
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hK : DerivedCategory.TStructure.t.minus K) :
    DerivedCategory.TStructure.t.minus (T.baseChange.obj K) := by
  obtain ⟨n, hn⟩ := hK
  exact ⟨n, T.isLE_baseChange_obj K n⟩

/-- **Derived base change on bounded above derived categories**, `D⁻(O) ⥤ D⁻(O₀)`. -/
def baseChangeMinus :
    DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤
      DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :=
  DerivedCategory.TStructure.t.minus.lift (DerivedCategory.Minus.ι ⋙ T.baseChange)
    (fun K ↦ T.minus_baseChange_obj K.obj K.property)

/-- The underlying object of the derived base change of a bounded above object. -/
@[simp]
theorem baseChangeMinus_obj_obj
    (K : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    (T.baseChangeMinus.obj K).obj = T.baseChange.obj K.obj := rfl

end DerivedExtensionOfScalars

end Deformation.ComplexLift
