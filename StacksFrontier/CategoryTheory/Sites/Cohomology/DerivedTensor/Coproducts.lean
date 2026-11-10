module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product commutes with arbitrary direct sums

Let `(C, 𝒪)` be a ringed site. For a fixed object `A` of `D(Mod(𝒪))` the functor
`A ⊗^𝐋_𝒪 - : D(Mod(𝒪)) ⥤ D(Mod(𝒪))` preserves direct sums indexed by an arbitrary type of the
module universe.

## Main results

* `Stacks.DerivedTensor.RingedSite.preservesColimitsOfShape_discrete_tensorComplex_obj`:
  `Tot(K ⊗_𝒪 -)` on cochain complexes preserves `I`-indexed direct sums.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonLeftFac`: for a K-flat complex
  `K`, the comparison `Q(K) ⊗^𝐋_𝒪 Q(-) ≅ Q(Tot(K ⊗_𝒪 -))` of [Stacks, Tag 06YU] read as an
  isomorphism of functors on cochain complexes.
* `Stacks.DerivedTensor.RingedSite.preservesColimitsOfShape_discrete_derivedTensorProductFunctor`:
  **`A ⊗^𝐋_𝒪 -` preserves `I`-indexed direct sums**, for an arbitrary `A` in `D(Mod(𝒪))`.

## Implementation notes

The argument is the one the module case uses in
`StacksFrontier/Homology/Tor/DerivedTensorDirectSum.lean`: move the direct sum to the level of
complexes, where the statement is degreewise.

Three steps. First, `Tot(K ⊗_𝒪 -)` preserves direct sums of complexes: the double complex
`(p, q) ↦ K^p ⊗_𝒪 (-)^q` does because `K^p ⊗_𝒪 -` does, tensoring with a fixed sheaf of modules
being a left adjoint (`Mod(𝒪)` is monoidal closed), and the total complex of a double complex
does because in each total degree it is a coproduct of bidegree evaluations; these are
`CochainComplex.KFlatBifunctor.preservesColimitsOfShape_mapBifunctorObj` and
`preservesColimitsOfShape_totalFunctor`.

Second, the K-flat comparison of [Stacks, Tag 06YU] — the field `comparisonLeft` of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, whose left-hand K-flatness hypothesis is
the only one — is natural in the right-hand complex, so it assembles into an isomorphism of
functors `Q ⋙ (Q(K) ⊗^𝐋_𝒪 -) ≅ Tot(K ⊗_𝒪 -) ⋙ Q`. Since `Q` preserves direct sums
([Stacks, Tag 07D9]) and is essentially surjective,
`preservesColimitsOfShape_discrete_of_essSurj_comp` transfers the property from the right-hand side
to `Q(K) ⊗^𝐋_𝒪 -`.

Third, an arbitrary object of `D(Mod(𝒪))` is isomorphic to `Q(K)` for a K-flat `K`, by the
existence of K-flat resolutions (`Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso`), and
the property only depends on the isomorphism class.

Nothing restricts the index type beyond the module universe, which is the universe in which
`D(Mod(𝒪))` has direct sums at all.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-! ### The total tensor complex with a fixed left factor -/

omit [(Stacks.SheafOfModules.Tensor.sheafTensor R : Modules R ⥤ Modules R ⥤ Modules R).Additive]
  [∀ M : Modules R, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)] in
/-- Tensoring on the left with a fixed sheaf of modules preserves `I`-indexed direct sums: it is
a left adjoint, `Mod(𝒪)` being monoidal closed.  This is [Stacks, Tag 05NB]. -/
theorem preservesColimitsOfShape_discrete_sheafTensor_obj (I : Type u) (M : Modules R) :
    PreservesColimitsOfShape (Discrete I)
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M) :=
  ⟨fun {_} => inferInstance⟩

/-- `Tot(K ⊗_𝒪 -)`, the functor on cochain complexes of `𝒪`-modules obtained from the total
tensor complex of [Stacks, Tag 06YM] by fixing the left factor, *is*
`CochainComplex.KFlatBifunctor.totFunctor` at the tensor product of sheaves of modules: both
send `L` to the total complex of `(p, q) ↦ K^p ⊗_𝒪 L^q` and a map `g` to the total map it
induces. -/
theorem tensorComplexObj_map (K : CochainComplex (Modules R) ℤ)
    {L L' : CochainComplex (Modules R) ℤ} (g : L ⟶ L') :
    ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K).map g =
      (CochainComplex.KFlatBifunctor.totFunctor
        (Stacks.SheafOfModules.Tensor.sheafTensor R) K).map g := by
  simp only [CochainComplex.KFlatBifunctor.totFunctor,
    Stacks.SheafOfModules.Tensor.tensorComplex, Functor.map₂HomologicalComplexReg_obj_map,
    HomologicalComplex.mapBifunctorMapReg, HomologicalComplex.mapBifunctorMap,
    Functor.comp_map, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rfl

/-- The identification of the previous lemma, read as an isomorphism of functors with identity
components. -/
def tensorComplexObjIso (K : CochainComplex (Modules R) ℤ) :
    (Stacks.SheafOfModules.Tensor.tensorComplex R).obj K ≅
      CochainComplex.KFlatBifunctor.totFunctor
        (Stacks.SheafOfModules.Tensor.sheafTensor R) K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} g => by
    simp only [Iso.refl_hom]
    exact (tensorComplexObj_map R K g).trans (Category.id_comp _).symm)

/-- **`Tot(K ⊗_𝒪 -)` preserves `I`-indexed direct sums of cochain complexes.**  The double
complex `(p, q) ↦ K^p ⊗_𝒪 (-)^q` does, because tensoring with a fixed sheaf of modules does and
colimits of complexes are computed degreewise, and the total complex of a double complex does
because in each total degree it is the coproduct of the bidegree evaluations. -/
theorem preservesColimitsOfShape_discrete_tensorComplex_obj (I : Type u)
    (K : CochainComplex (Modules R) ℤ) :
    PreservesColimitsOfShape (Discrete I)
      ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K) := by
  have h₁ := CochainComplex.KFlatBifunctor.preservesColimitsOfShape_mapBifunctorObj
    (J := Discrete I) (Stacks.SheafOfModules.Tensor.sheafTensor R) K
    (fun M => preservesColimitsOfShape_discrete_sheafTensor_obj R I M)
  have h₂ : PreservesColimitsOfShape (Discrete I)
      (HomologicalComplex₂.totalFunctor (Modules R) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)) :=
    CochainComplex.KFlatBifunctor.preservesColimitsOfShape_totalFunctor
  have h₃ : PreservesColimitsOfShape (Discrete I)
      (CochainComplex.KFlatBifunctor.totFunctor
        (Stacks.SheafOfModules.Tensor.sheafTensor R) K) :=
    comp_preservesColimitsOfShape _ _
  exact preservesColimitsOfShape_of_natIso (tensorComplexObjIso R K).symm

variable [HasDerivedCategory (Modules R)]

namespace DerivedTensorProduct

variable (T : DerivedTensorProduct R)

/-- **The K-flat comparison of [Stacks, Tag 06YU] as an isomorphism of functors.**  For a K-flat
complex `K` of `𝒪`-modules, the comparison `Q(K) ⊗^𝐋_𝒪 Q(L) ≅ Q(Tot(K ⊗_𝒪 L))` is natural in
`L`, by the field `comparisonLeft_naturality` at the identity of `K`. -/
def comparisonLeftFac (K : CochainComplex (Modules R) ℤ)
    (hK : Stacks.SheafOfModules.KFlat R K) :
    DerivedCategory.Q ⋙ T.tensor.obj (DerivedCategory.Q.obj K) ≅
      (Stacks.SheafOfModules.Tensor.tensorComplex R).obj K ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun L => T.comparisonLeft K L hK) (fun {L L'} g => by
    have h := T.comparisonLeft_naturality (K := K) (K' := K) (L := L) (L' := L')
      (𝟙 K) g hK hK
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h
    exact h)

/-- **`Q(K) ⊗^𝐋_𝒪 -` preserves `I`-indexed direct sums**, for a K-flat complex `K`.  The
comparison `comparisonLeftFac` identifies it, after precomposition with the localization `Q`,
with `Tot(K ⊗_𝒪 -)` followed by `Q`; both factors preserve direct sums, and `Q` is essentially
surjective, so the property descends. -/
theorem preservesColimitsOfShape_discrete_tensor_obj_Q (I : Type u)
    (K : CochainComplex (Modules R) ℤ)
    (hK : Stacks.SheafOfModules.KFlat R K) :
    PreservesColimitsOfShape (Discrete I) (T.tensor.obj (DerivedCategory.Q.obj K)) := by
  have hten := preservesColimitsOfShape_discrete_tensorComplex_obj R I K
  have hQ : PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := Modules R)) :=
    inferInstance
  have hrhs : PreservesColimitsOfShape (Discrete I)
      ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K ⋙
        DerivedCategory.Q (C := Modules R)) :=
    comp_preservesColimitsOfShape _ _
  have hfac : PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙ T.tensor.obj (DerivedCategory.Q.obj K)) :=
    preservesColimitsOfShape_of_natIso (comparisonLeftFac R T K hK).symm
  exact preservesColimitsOfShape_discrete_of_essSurj_comp
    (DerivedCategory.Q (C := Modules R)) (T.tensor.obj (DerivedCategory.Q.obj K)) I

/-- **The derived tensor product commutes with arbitrary direct sums.**  For an arbitrary object
`A` of `D(Mod(𝒪))` the functor `A ⊗^𝐋_𝒪 -` preserves `I`-indexed direct sums: `A` is isomorphic
to the class of a K-flat complex, where this is
`preservesColimitsOfShape_discrete_tensor_obj_Q`. -/
theorem preservesColimitsOfShape_discrete_tensor_obj (I : Type u)
    (A : DerivedCategory (Modules R)) :
    PreservesColimitsOfShape (Discrete I) (T.tensor.obj A) := by
  obtain ⟨P, f, hP, hf⟩ := exists_kFlat_quasiIso R (DerivedCategory.Q.objPreimage A)
  have e : DerivedCategory.Q.obj P ≅ A :=
    (asIso (DerivedCategory.Q.map f)).trans (DerivedCategory.Q.objObjPreimageIso A)
  have := preservesColimitsOfShape_discrete_tensor_obj_Q R T I P hP
  exact preservesColimitsOfShape_of_natIso (T.tensor.mapIso e)

end DerivedTensorProduct

/-- **The derived tensor product of sheaves of modules on a ringed site commutes with arbitrary
direct sums**, in the second variable: for an arbitrary `A` in `D(Mod(𝒪))` the functor
`A ⊗^𝐋_𝒪 -` preserves direct sums indexed by any type of the module universe. -/
@[stacks 06YU "the derived tensor product commutes with arbitrary direct sums in the second \
variable"]
theorem preservesColimitsOfShape_discrete_derivedTensorProductFunctor
    (I : Type u)
    (A : DerivedCategory (Modules R)) :
    PreservesColimitsOfShape (Discrete I) ((derivedTensorProductFunctor R).obj A) :=
  DerivedTensorProduct.preservesColimitsOfShape_discrete_tensor_obj R
    (canonicalDerivedTensorProduct R) I A

end Stacks.DerivedTensor.RingedSite

end
