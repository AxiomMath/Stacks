module

public import StacksFrontier.Deformation.ToposThickening.DerivedLiftObstruction
public import StacksFrontier.Deformation.ToposThickening.DerivedLiftBaseChange
public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsMinus

/-!
# Shifting lifts of a bounded above complex

Let `T` be a derived base change along `f : O ⟶ O₀` commuting with the shift. A lift `(K, α)` of
`K₀` (Stacks 0DIZ) gives the lift `(K⟦m⟧, α⟦m⟧)` of any `K₀'` with `K₀⟦m⟧ ≅ K₀'`
(`Deformation.ComplexLift.DerivedLift.shift`). This respects isomorphy of lifts in both
directions (`Deformation.ComplexLift.DerivedLift.isomorphic_shift_iff`), so it induces an
injective map of isomorphism classes of lifts
(`Deformation.ComplexLift.DerivedLift.classShift`,
`Deformation.ComplexLift.DerivedLift.classShift_injective`), and it commutes with base change of
lifts along a `Deformation.ComplexLift.DerivedReductionBaseChange` whose functor and comparison
commute with the shift (`Deformation.ComplexLift.DerivedLift.isomorphic_baseChange_shift`,
`Deformation.ComplexLift.DerivedLift.liftClassMap_classShift`). The derived base change
`Deformation.ComplexLift.derivedExtensionOfScalarsData` commutes with the shift, being left adjoint
to restriction of scalars (`Deformation.ComplexLift.derivedExtensionOfScalarsData_commShift`).

The `k`-linear groups `Hom(K, K⟦n⟧)` do not change under the shift
(`Deformation.ComplexLift.finiteDimensional_shift_hom_shift`,
`Deformation.ComplexLift.finiteDimensional_shift_hom_self`).

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe d d' d₀ v' u u'

section HomShift

variable (k : Type*) [Field k] {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [Linear k 𝒟]
  [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [∀ n : ℤ, (shiftFunctor 𝒟 n).Linear k]

/-- The `k`-linear map `Hom(K, K⟦n⟧) ⟶ Hom(K⟦m⟧, K⟦m⟧⟦n⟧)`, `φ ↦ φ⟦m⟧` followed by the
commutation of the two shifts. -/
def shiftHomLinearMap (K : 𝒟) (m n : ℤ) : (K ⟶ K⟦n⟧) →ₗ[k] (K⟦m⟧ ⟶ K⟦m⟧⟦n⟧) where
  toFun φ := φ⟦m⟧' ≫ (shiftFunctorComm 𝒟 m n).inv.app K
  map_add' φ ψ := by rw [Functor.map_add, Preadditive.add_comp]
  map_smul' c φ := by rw [Functor.map_smul, Linear.smul_comp, RingHom.id_apply]

/-- The `k`-linear map `Hom(K, K⟦n⟧) ⟶ Hom(K⟦m⟧, K⟦m⟧⟦n⟧)` given by shifting is surjective. -/
theorem shiftHomLinearMap_surjective (K : 𝒟) (m n : ℤ) :
    Function.Surjective (shiftHomLinearMap k K m n) := by
  intro g
  refine ⟨(shiftFunctor 𝒟 m).preimage (g ≫ (shiftFunctorComm 𝒟 m n).hom.app K), ?_⟩
  show (shiftFunctor 𝒟 m).map ((shiftFunctor 𝒟 m).preimage _) ≫ _ = g
  rw [Functor.map_preimage, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id g

/-- **`Hom(K⟦m⟧, K⟦m⟧⟦n⟧)` is finite dimensional when `Hom(K, K⟦n⟧)` is**: the shift is a
`k`-linear equivalence. -/
theorem finiteDimensional_shift_hom_shift (K : 𝒟) (m n : ℤ) [FiniteDimensional k (K ⟶ K⟦n⟧)] :
    FiniteDimensional k (K⟦m⟧ ⟶ K⟦m⟧⟦n⟧) :=
  Module.Finite.of_surjective (shiftHomLinearMap k K m n) (shiftHomLinearMap_surjective k K m n)

/-- **`Hom(K⟦m⟧, K⟦m⟧)` is finite dimensional when `Hom(K, K)` is.** -/
theorem finiteDimensional_shift_hom_self (K : 𝒟) (m : ℤ) [FiniteDimensional k (K ⟶ K)] :
    FiniteDimensional k (K⟦m⟧ ⟶ K⟦m⟧) :=
  Module.Finite.of_surjective (Functor.mapLinearMap k (shiftFunctor 𝒟 m) (X := K) (Y := K))
    (shiftFunctor 𝒟 m).map_surjective

end HomShift

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀}
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- **A derived base change commutes with the shift**: it is left adjoint to restriction of
scalars (`Deformation.ComplexLift.derivedAdjunctionOf`), which does. -/
abbrev derivedExtensionOfScalarsCommShift (T : DerivedExtensionOfScalars.{d, d₀} f) :
    T.baseChange.CommShift ℤ :=
  (derivedAdjunctionOf.{d, d₀} f T).leftAdjointCommShift ℤ

/-- The derived base change `Deformation.ComplexLift.derivedExtensionOfScalarsData` commutes with
the shift. -/
instance derivedExtensionOfScalarsData_commShift :
    (derivedExtensionOfScalarsData.{d, d₀} f).baseChange.CommShift ℤ :=
  derivedExtensionOfScalarsCommShift _

namespace DerivedLift

variable {T : DerivedExtensionOfScalars.{d, d₀} f} [T.baseChange.CommShift ℤ]
  {K₀ K₀' : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}

/-- **The shift of a lift.** A lift `(K, α)` of `K₀` gives the lift `(K⟦m⟧, α⟦m⟧)` of any `K₀'`
identified with `K₀⟦m⟧`, through `T(K⟦m⟧) ≅ T(K)⟦m⟧`. -/
def shift (L : DerivedLift T K₀) (m : ℤ) (e : K₀.obj⟦m⟧ ≅ K₀'.obj) : DerivedLift T K₀' where
  K := ⟨L.K.obj⟦m⟧, DerivedCategory.TStructure.t.minus.le_shift m _ L.K.property⟩
  identification := (T.baseChange.commShiftIso m).app L.K.obj ≪≫
    (shiftFunctor _ m).mapIso L.identification ≪≫ e

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The identification of the shifted lift `L.shift m e` is the composite
`T(K⟦m⟧) ≅ T(K)⟦m⟧ ≅ K₀⟦m⟧ ≅ K₀'`. -/
theorem shift_identification_hom (L : DerivedLift T K₀) (m : ℤ) (e : K₀.obj⟦m⟧ ≅ K₀'.obj) :
    (L.shift m e).identification.hom = (T.baseChange.commShiftIso m).hom.app L.K.obj ≫
      L.identification.hom⟦m⟧' ≫ e.hom :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Shifting lifts respects and reflects isomorphy.** An isomorphism of shifted lifts is the
shift of a unique isomorphism of the lifts, the shift being an equivalence, and it is compatible
with the identifications if and only if that one is, the shift being faithful. -/
theorem isomorphic_shift_iff (L₁ L₂ : DerivedLift T K₀) (m : ℤ) (e : K₀.obj⟦m⟧ ≅ K₀'.obj) :
    Isomorphic (L₁.shift m e) (L₂.shift m e) ↔ Isomorphic L₁ L₂ := by
  have key : ∀ ψ : L₁.K.obj ⟶ L₂.K.obj,
      (T.baseChange.map (ψ⟦m⟧') ≫ (L₂.shift m e).identification.hom =
        (L₁.shift m e).identification.hom ↔
        T.baseChange.map ψ ≫ L₂.identification.hom = L₁.identification.hom) := by
    intro ψ
    rw [shift_identification_hom, shift_identification_hom,
      Functor.commShiftIso_hom_naturality_assoc, cancel_epi, ← Functor.map_comp_assoc,
      cancel_mono]
    exact (shiftFunctor _ m).map_injective.eq_iff
  constructor
  · rintro ⟨φ, hφ⟩
    let ψ : L₁.K.obj ≅ L₂.K.obj := (shiftFunctor _ m).preimageIso φ
    refine ⟨ψ, (key ψ.hom).1 ?_⟩
    have : ψ.hom⟦m⟧' = φ.hom := (shiftFunctor _ m).map_preimage φ.hom
    rw [this]
    exact hφ
  · rintro ⟨ψ, hψ⟩
    exact ⟨(shiftFunctor _ m).mapIso ψ, (key ψ.hom).2 hψ⟩

/-- **Shifting isomorphism classes of lifts**, the map of classes induced by
`Deformation.ComplexLift.DerivedLift.shift`. -/
def classShift (m : ℤ) (e : K₀.obj⟦m⟧ ≅ K₀'.obj) :
    Quotient (setoid.{d, d₀, v', u, u'} (T := T) (K₀ := K₀)) →
      Quotient (setoid.{d, d₀, v', u, u'} (T := T) (K₀ := K₀')) :=
  Quotient.map (fun L => L.shift m e) fun L₁ L₂ h => (isomorphic_shift_iff L₁ L₂ m e).2 h

/-- The shift of the class of a lift `L` is the class of `L.shift m e`. -/
theorem classShift_mk (m : ℤ) (e : K₀.obj⟦m⟧ ≅ K₀'.obj) (L : DerivedLift T K₀) :
    classShift m e (Quotient.mk _ L) = Quotient.mk _ (L.shift m e) :=
  rfl

/-- Shifting isomorphism classes of lifts is injective. -/
theorem classShift_injective (m : ℤ) (e : K₀.obj⟦m⟧ ≅ K₀'.obj) :
    Function.Injective (classShift (T := T) m e) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h L₁ =>
    induction b using Quotient.inductionOn with
    | h L₂ =>
      exact Quotient.sound ((isomorphic_shift_iff L₁ L₂ m e).1 (Quotient.exact hab))

end DerivedLift

section BaseChange

variable {O O' O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀} {f' : O' ⟶ O₀}
variable
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable {T : DerivedExtensionOfScalars.{d, d₀} f} {T' : DerivedExtensionOfScalars.{d', d₀} f'}
  [T.baseChange.CommShift ℤ] [T'.baseChange.CommShift ℤ]
  {idealTensor idealTensor' :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}
  {R : DerivedReduction T idealTensor} {R' : DerivedReduction T' idealTensor'}
  (B : DerivedReductionBaseChange R R') [B.functor.CommShift ℤ]
  [NatTrans.CommShift B.baseChangeIso.hom ℤ]
  {K₀ K₀' : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}

namespace DerivedLift

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Shifting lifts commutes with base change**, for a base change whose functor and comparison
commute with the shift: the comparison `β(K⟦m⟧) ≅ (β K)⟦m⟧` is an isomorphism of lifts. -/
theorem isomorphic_baseChange_shift (L : DerivedLift T K₀) (m : ℤ) (e : K₀.obj⟦m⟧ ≅ K₀'.obj) :
    Isomorphic ((L.shift m e).baseChange B) ((L.baseChange B).shift m e) := by
  refine ⟨(B.functor.commShiftIso m).app L.K.obj, ?_⟩
  have h := NatTrans.shift_app_comm B.baseChangeIso.hom m L.K.obj
  rw [Functor.commShiftIso_comp_hom_app] at h
  show T'.baseChange.map ((B.functor.commShiftIso m).hom.app L.K.obj) ≫
      (T'.baseChange.commShiftIso m).hom.app (B.functor.obj L.K.obj) ≫
      (B.baseChangeIso.hom.app L.K.obj ≫ L.identification.hom)⟦m⟧' ≫ e.hom =
    B.baseChangeIso.hom.app (L.K.obj⟦m⟧) ≫ (T.baseChange.commShiftIso m).hom.app L.K.obj ≫
      L.identification.hom⟦m⟧' ≫ e.hom
  rw [Functor.map_comp, Category.assoc, reassoc_of% h]

/-- Shifting classes of lifts commutes with base change of classes. -/
theorem liftClassMap_classShift (m : ℤ) (e : K₀.obj⟦m⟧ ≅ K₀'.obj)
    (a : Quotient (setoid.{d, d₀, v', u, u'} (T := T) (K₀ := K₀))) :
    B.liftClassMap (classShift m e a) = classShift m e (B.liftClassMap a) := by
  induction a using Quotient.inductionOn with
  | h L => exact Quotient.sound (isomorphic_baseChange_shift B L m e)

end DerivedLift

end BaseChange

end Deformation.ComplexLift

end
