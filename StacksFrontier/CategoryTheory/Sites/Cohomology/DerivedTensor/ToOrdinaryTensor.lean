module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Bifunctor
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map from the derived to the ordinary tensor product

Let `(C, O)` be a ringed site. For arbitrary complexes `K` and `L` of `O`-modules there is a
canonical map

`K ⊗^L_O L ⟶ Tot(K ⊗_O L)`

in `D(Mod(O))`, natural in both complexes, which is an isomorphism as soon as either complex
is K-flat. It is defined by choosing a K-flat resolution `p : P ⟶ K` and composing the
inverse of `P ⊗^L_O L ≅ K ⊗^L_O L` with the comparison `P ⊗^L_O L ≅ Tot(P ⊗_O L)` and with
`Tot(p ⊗ 1_L)`. This is the map of Stacks 0FPH.

The content of this file is that the result does not depend on the chosen resolution, in the
strong form that it is *natural*: the defining property

`(p ⊗^L 1) ≫ toTensor = comparison ≫ Tot(a ⊗ 1)`

holds not only for the chosen resolution but for an arbitrary map `a : A ⟶ K` out of a K-flat
complex `A`. That is `toTensor_comp_of_kFlat`, and everything else follows from it.

## Main definitions

* `Stacks.SheafOfModules.kFlatRes` and `kFlatResMap`: a chosen K-flat resolution of a complex.
* `Stacks.SheafOfModules.toTensor`: the canonical map.

## Main results

* `Stacks.SheafOfModules.toTensor_comp_of_kFlat`: the defining property, for an arbitrary map
  out of a K-flat complex.
* `Stacks.SheafOfModules.toTensor_naturality`: naturality in both complexes.
* `Stacks.SheafOfModules.isIso_toTensor_of_kFlat_left` and `isIso_toTensor_of_kFlat_right`:
  the canonical map is an isomorphism as soon as either factor is K-flat.

## Implementation notes

The proof of `toTensor_comp_of_kFlat` is where the resolution-independence lives. Given
`a : A ⟶ K` with `A` K-flat and the chosen resolution `p : P ⟶ K`, the right Ore condition for
the quasi-isomorphisms of the homotopy category completes the cospan `A → K ← P` to a commuting
square with a quasi-isomorphism `W ⟶ A`; replacing `W` by a K-flat resolution of it makes the
upper-left corner K-flat as well. Both sides of the asserted equation, precomposed with the
isomorphism that this quasi-isomorphism induces, then reduce to the comparison at that corner
followed by the same map of total tensor complexes — the two maps of complexes being only
homotopic, which is enough because the total tensor product with a fixed complex factors
through the homotopy category (Stacks 06YM).

Naturality is then formal: precomposing with the isomorphism induced by the chosen resolution
of the source, both sides of the naturality square reduce to `toTensor_comp_of_kFlat` applied
to the composite of the resolution with the given map.

The universes are all equal, inherited from the existence of K-flat resolutions.

## References

* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YT](https://stacks.math.columbia.edu/tag/06YT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- A chosen K-flat resolution of a complex of sheaves of modules. -/
def kFlatRes (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  ℤ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (exists_kFlat_quasiIso X K).choose

/-- The augmentation of the chosen K-flat resolution. -/
def kFlatResMap (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
  X.O)) ℤ) :
    kFlatRes X K ⟶ K :=
  (exists_kFlat_quasiIso X K).choose_spec.choose

/-- The chosen K-flat resolution is K-flat. -/
theorem isKFlat_kFlatRes
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsKFlat X.O (kFlatRes X K) :=
  (exists_kFlat_quasiIso X K).choose_spec.choose_spec.1

/-- The augmentation of the chosen K-flat resolution is a quasi-isomorphism. -/
instance quasiIso_kFlatResMap
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (kFlatResMap X K) :=
  (exists_kFlat_quasiIso X K).choose_spec.choose_spec.2

variable [HasDerivedCategory.{d}
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))]

attribute [local instance] kFlatQ_isLocalization derivedTensorBifunctorLifting

section Comparison

/-- The comparison isomorphism is natural in the K-flat variable alone. -/
theorem kFlatComparison_naturality_left
    {A B L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : IsKFlat X.O A) (hB : IsKFlat X.O B) (c : A ⟶ B) :
    ((derivedTensorBifunctor X).map (DerivedCategory.Q.map c)).app
          (DerivedCategory.Q.obj L) ≫ (kFlatComparison X B hB L).hom =
      (kFlatComparison X A hA L).hom ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map c).app L) := by
  simpa using kFlatComparison_naturality X hA hB c (𝟙 L)

end Comparison

/-- The isomorphism of derived tensor products induced by the chosen K-flat resolution of the
first factor. -/
instance isIso_derivedTensor_map_kFlatResMap
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (((derivedTensorBifunctor X).map
      (DerivedCategory.Q.map (kFlatResMap X K))).app (DerivedCategory.Q.obj L)) := by
  have : IsIso (DerivedCategory.Q.map (kFlatResMap X K)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  infer_instance

/-- The canonical map from the derived tensor product to the ordinary total tensor product.
It is defined through the chosen K-flat resolution of the first factor;
`toTensor_comp_of_kFlat` shows that any map out of a K-flat complex computes it. -/
def toTensor (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  ℤ) :
    ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) :=
  inv (((derivedTensorBifunctor X).map
      (DerivedCategory.Q.map (kFlatResMap X K))).app (DerivedCategory.Q.obj L)) ≫
    (kFlatComparison X (kFlatRes X K) (isKFlat_kFlatRes X K) L).hom ≫
    DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (kFlatResMap X
      K)).app L)

/-- The defining property of `toTensor`, for the chosen resolution. -/
theorem toTensor_comp_kFlatResMap
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedTensorBifunctor X).map
          (DerivedCategory.Q.map (kFlatResMap X K))).app (DerivedCategory.Q.obj L) ≫
        toTensor X K L =
      (kFlatComparison X (kFlatRes X K) (isKFlat_kFlatRes X K) L).hom ≫
        DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (kFlatResMap X K)).app L) := by
  rw [toTensor, IsIso.hom_inv_id_assoc]

/-- **The defining property of `toTensor`.** For *any* map `a : A ⟶ K` out of a K-flat
complex `A`, precomposing `toTensor` with the induced map of derived tensor products gives the
comparison at `A` followed by the ordinary total tensor of `a`. In particular the value of
`toTensor` does not depend on the chosen resolution. -/
theorem toTensor_comp_of_kFlat
    {A K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : IsKFlat X.O A) (a : A ⟶ K)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedTensorBifunctor X).map (DerivedCategory.Q.map a)).app
          (DerivedCategory.Q.obj L) ≫ toTensor X K L =
      (kFlatComparison X A hA L).hom ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map a).app L) := by
  obtain ⟨hsat, _⟩ := quasiIso_isSaturated_and_isCompatibleWithTriangulation.{c, u, u} X.O
  have := hsat.hasRightCalculusOfFractions
  obtain ⟨ψ, hψ⟩ := MorphismProperty.HasRightCalculusOfFractions.exists_rightFraction
    (W := HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (MorphismProperty.LeftFraction.mk
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (kFlatResMap X K))
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (quasiIso_kFlatResMap X K)))
  have hψ' : ψ.s ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a =
      ψ.f ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (kFlatResMap X K) := hψ
  obtain ⟨W', ρ, hW', hρ⟩ := exists_kFlat_quasiIso X ψ.X'.as
  obtain ⟨s₀, hs₀⟩ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_surjective ψ.s
  obtain ⟨f₀, hf₀⟩ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_surjective ψ.f
  have hs₀Q : QuasiIso s₀ := by
    refine (HomotopyCategory.quotient_map_mem_quasiIso_iff s₀).1 ?_
    rw [hs₀]
    exact ψ.hs
  obtain ⟨w, v, hwQ, hsq⟩ : ∃ (w : W' ⟶ A) (v : W' ⟶ kFlatRes X K), QuasiIso w ∧
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (w ≫ a) =
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (v ≫ kFlatResMap X K) := by
    have hρQ : QuasiIso ρ := hρ
    refine ⟨ρ ≫ s₀, ρ ≫ f₀, inferInstance, ?_⟩
    have h1 : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (s₀ ≫ a) =
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (f₀ ≫ kFlatResMap X K) := by
      rw [Functor.map_comp, Functor.map_comp, hs₀, hf₀]
      exact hψ'
    rw [Category.assoc, Category.assoc, Functor.map_comp _ ρ (s₀ ≫ a),
      Functor.map_comp _ ρ (f₀ ≫ kFlatResMap X K), h1]
  have htot : DerivedCategory.Q.map
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (w ≫ a)).app L) =
      DerivedCategory.Q.map
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (v ≫ kFlatResMap X K)).app L) := by
    refine DerivedCategory.Q_map_eq_of_homotopy _ (HomotopyCategory.homotopyOfEq _ _ ?_)
    have e : ∀ f : W' ⟶ K,
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app L) =
          (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) L).map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f) := fun _ ↦ rfl
    rw [e, e, hsq]
  have hQ : DerivedCategory.Q.map (w ≫ a) =
      DerivedCategory.Q.map (v ≫ kFlatResMap X K) :=
    DerivedCategory.Q_map_eq_of_homotopy _ (HomotopyCategory.homotopyOfEq _ _ hsq)
  have hwIso : IsIso (DerivedCategory.Q.map w) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hwQ
  have key₂ : ((derivedTensorBifunctor X).map
        (DerivedCategory.Q.map w)).app (DerivedCategory.Q.obj L) ≫
      (kFlatComparison X A hA L).hom ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map a).app L) =
      (kFlatComparison X W' hW' L).hom ≫
        DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (w ≫ a)).app L) := by
    rw [← Category.assoc, kFlatComparison_naturality_left X hW' hA w, Category.assoc,
      ← Functor.map_comp, ← NatTrans.comp_app, ← Functor.map_comp]
  have key₁ : ((derivedTensorBifunctor X).map
        (DerivedCategory.Q.map w)).app (DerivedCategory.Q.obj L) ≫
      ((derivedTensorBifunctor X).map (DerivedCategory.Q.map a)).app
          (DerivedCategory.Q.obj L) ≫ toTensor X K L =
      (kFlatComparison X W' hW' L).hom ≫
        DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (v ≫ kFlatResMap X K)).app L) := by
    rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp, hQ,
      Functor.map_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc,
      toTensor_comp_kFlatResMap X K L, ← Category.assoc,
      kFlatComparison_naturality_left X hW' (isKFlat_kFlatRes X K) v, Category.assoc,
      ← Functor.map_comp, ← NatTrans.comp_app, ← Functor.map_comp]
  rw [← cancel_epi (((derivedTensorBifunctor X).map
    (DerivedCategory.Q.map w)).app (DerivedCategory.Q.obj L)), key₁, key₂, htot]

/-- The comparison isomorphism is natural in the arbitrary variable alone. -/
theorem kFlatComparison_naturality_right
    {A L L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : IsKFlat X.O A) (g : L ⟶ L') :
    ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)).map
          (DerivedCategory.Q.map g) ≫ (kFlatComparison X A hA L').hom =
      (kFlatComparison X A hA L).hom ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map g) := by
  simpa using kFlatComparison_naturality X hA hA (𝟙 A) g

/-- `toTensor` is invertible once the total tensor of the resolution augmentation is a
quasi-isomorphism. -/
private theorem isIso_toTensor_of_quasiIso
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (h : QuasiIso (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map
      (kFlatResMap X K)).app L)) : IsIso (toTensor X K L) := by
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h
  rw [toTensor]
  infer_instance

/-- The canonical map is an isomorphism when the right factor is K-flat: the only
non-invertible ingredient of its definition is the total tensor of the resolution
augmentation, and Stacks 06YP makes that a quasi-isomorphism. -/
theorem isIso_toTensor_of_kFlat_right
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : IsKFlat X.O L) : IsIso (toTensor X K L) :=
  isIso_toTensor_of_quasiIso X K L
    (IsKFlat.quasiIso_tensorComplex_map_app X.O L hL (kFlatResMap X K) (quasiIso_kFlatResMap X K))

/-- The canonical map is an isomorphism when the left factor is K-flat: the resolution
augmentation is then a quasi-isomorphism of K-flat complexes, and Stacks 06YT makes its total
tensor with an arbitrary complex a quasi-isomorphism. -/
theorem isIso_toTensor_of_kFlat_left
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : IsKFlat X.O K) : IsIso (toTensor X K L) :=
  isIso_toTensor_of_quasiIso X K L
    (quasiIso_tensorComplex_map_app_of_kFlat X (kFlatResMap X K)
      (quasiIso_kFlatResMap X K) (isKFlat_kFlatRes X K) hK L)

/-- **Naturality of the canonical map** in both complexes, with no K-flatness hypothesis. -/
theorem toTensor_naturality
    {K K' L L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedTensorBifunctor X).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj K')).map
          (DerivedCategory.Q.map g) ≫
        toTensor X K' L' =
      toTensor X K L ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app L ≫
          ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K').map g) := by
  have hP := isKFlat_kFlatRes X K
  have hcomplex : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj (kFlatRes X K)).map g ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (kFlatResMap X K ≫ f)).app L' =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (kFlatResMap X K)).app L ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app L ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K').map g := by
    rw [Functor.map_comp, NatTrans.comp_app,
      ← Category.assoc, ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (kFlatResMap X
        K)).naturality g,
      Category.assoc, ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).naturality g]
  rw [← cancel_epi (((derivedTensorBifunctor X).map
    (DerivedCategory.Q.map (kFlatResMap X K))).app (DerivedCategory.Q.obj L))]
  rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
    ← Category.assoc,
    ← ((derivedTensorBifunctor X).map
      (DerivedCategory.Q.map (kFlatResMap X K ≫ f))).naturality (DerivedCategory.Q.map g),
    Category.assoc,
    toTensor_comp_of_kFlat X hP (kFlatResMap X K ≫ f) L',
    ← Category.assoc, kFlatComparison_naturality_right X hP g, Category.assoc,
    ← Functor.map_comp, ← Category.assoc, toTensor_comp_of_kFlat X hP (kFlatResMap X K) L,
    Category.assoc, ← Functor.map_comp, hcomplex]

end Stacks.SheafOfModules

end
