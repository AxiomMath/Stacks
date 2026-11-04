module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaComponent

/-!
# The derived tensor product with a K-flat complex

Let `T` be a derived tensor product on `D(R)` and `E` a K-flat complex of `R`-modules. Then
`Q(E) ⊗ᴸ Q(X) ≅ Q(E ⊗ X)` for *every* complex `X`, naturally in `X`, and on K-flat `X` this is
the comparison isomorphism of `T`. Only the first factor needs to be K-flat.

## Main definitions

* `CochainComplex.DerivedTensor.DerivedTensorProduct.kFlatLeftComparison`: the natural
  isomorphism `Q(E) ⊗ᴸ Q(-) ≅ Q(E ⊗ -)` of functors on complexes.

## Main results

* `CochainComplex.DerivedTensor.DerivedTensorProduct.kFlatLeftComparison_app_of_kFlat`: on a
  K-flat complex it is the comparison of `T`.

## References

* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace CochainComplex.DerivedTensor.DerivedTensorProduct

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] (T : DerivedTensorProduct R)

/-- Tensoring on the left with a K-flat complex inverts quasi-isomorphisms. -/
theorem tensorLeft_inverts_of_kFlat (E : CochainComplex (ModuleCat.{u} R) ℤ) (hE : E.KFlat) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).IsInvertedBy
      (tensorLeft E ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : QuasiIso f := hf
  have : QuasiIso ((tensorLeft E).map f) := StacksDraft.TorAmplitude.quasiIso_tensorLeft_map E hE f
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((tensorLeft E).map f)))

/-- The descent of `E ⊗ -` to `D(R)`, for `E` K-flat. -/
abbrev kFlatLeftLift (E : CochainComplex (ModuleCat.{u} R) ℤ) (hE : E.KFlat) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift (tensorLeft E ⋙ DerivedCategory.Q) (tensorLeft_inverts_of_kFlat E hE)
    DerivedCategory.Q

/-- The comparison of `T` at `(E, X)`, read into the descent of `E ⊗ -`. -/
abbrev kFlatLeftLiftComponent (E : CochainComplex (ModuleCat.{u} R) ℤ) (hE : E.KFlat)
    (X : CochainComplex (ModuleCat.{u} R) ℤ) (hX : X.KFlat) :
    (T.tensor.obj (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj X) ≅
      (kFlatLeftLift E hE).obj (DerivedCategory.Q.obj X) :=
  T.comparison E X hE hX ≪≫
    ((Localization.fac (tensorLeft E ⋙ DerivedCategory.Q) (tensorLeft_inverts_of_kFlat E hE)
      DerivedCategory.Q).app X).symm

/-- The components `kFlatLeftLiftComponent` are natural in morphisms `g : X ⟶ Y` of K-flat
complexes. -/
theorem kFlatLeftLiftComponent_naturality (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (hE : E.KFlat) (X Y : CochainComplex (ModuleCat.{u} R) ℤ) (hX : X.KFlat) (hY : Y.KFlat)
    (g : X ⟶ Y) :
    (T.tensor.obj (DerivedCategory.Q.obj E)).map (DerivedCategory.Q.map g) ≫
        (T.kFlatLeftLiftComponent E hE Y hY).hom =
      (T.kFlatLeftLiftComponent E hE X hX).hom ≫
        (kFlatLeftLift E hE).map (DerivedCategory.Q.map g) := by
  have h := T.comparison_naturality (𝟙 E) g hE hE hX hY
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h
  have hf := (Localization.fac (tensorLeft E ⋙ DerivedCategory.Q)
    (tensorLeft_inverts_of_kFlat E hE) DerivedCategory.Q).inv.naturality g
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
  rw [reassoc_of% h, Category.assoc]
  exact congrArg ((T.comparison E X hE hX).hom ≫ ·) hf

/-- The derived tensor product with `Q(E)` agrees with the descent of `E ⊗ -`. -/
def kFlatLeftLiftIso (E : CochainComplex (ModuleCat.{u} R) ℤ) (hE : E.KFlat) :
    T.tensor.obj (DerivedCategory.Q.obj E) ≅ kFlatLeftLift E hE :=
  ModuleSystemRlimTensor.natIsoOfResolutions (fun X => X.KFlat)
    (fun X => by
      obtain ⟨P, s, hP, -, hs, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} X
      exact ⟨P, s, hP, hs⟩)
    (T.tensor.obj (DerivedCategory.Q.obj E)) (kFlatLeftLift E hE)
    (fun X hX => T.kFlatLeftLiftComponent E hE X hX)
    (fun X Y hX hY g => T.kFlatLeftLiftComponent_naturality E hE X Y hX hY g)

/-- **The derived tensor product with a K-flat complex**: `Q(E) ⊗ᴸ Q(X) ≅ Q(E ⊗ X)`, naturally
in the complex `X`. -/
def kFlatLeftComparison (E : CochainComplex (ModuleCat.{u} R) ℤ) (hE : E.KFlat) :
    DerivedCategory.Q ⋙ T.tensor.obj (DerivedCategory.Q.obj E) ≅
      tensorLeft E ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q (T.kFlatLeftLiftIso E hE) ≪≫
    Localization.fac (tensorLeft E ⋙ DerivedCategory.Q) (tensorLeft_inverts_of_kFlat E hE)
      DerivedCategory.Q

/-- On a K-flat complex the comparison is that of `T`. -/
theorem kFlatLeftComparison_app_of_kFlat (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (hE : E.KFlat) (X : CochainComplex (ModuleCat.{u} R) ℤ)
    (hX : X.KFlat) :
    (T.kFlatLeftComparison E hE).app X = T.comparison E X hE hX := by
  ext
  have h := ModuleSystemRlimTensor.natIsoOfResolutions_hom_app_of_prop (fun X => X.KFlat)
    (fun X => by
      obtain ⟨P, s, hP, -, hs, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} X
      exact ⟨P, s, hP, hs⟩)
    (T.tensor.obj (DerivedCategory.Q.obj E)) (kFlatLeftLift E hE)
    (fun X hX => T.kFlatLeftLiftComponent E hE X hX)
    (fun X Y hX hY g => T.kFlatLeftLiftComponent_naturality E hE X Y hX hY g) X hX
  show (T.kFlatLeftLiftIso E hE).hom.app (DerivedCategory.Q.obj X) ≫ _ = _
  rw [kFlatLeftLiftIso, h]
  simp

end CochainComplex.DerivedTensor.DerivedTensorProduct

end
