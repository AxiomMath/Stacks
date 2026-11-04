module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.Homology.KFlat.BifunctorTransportEquivalence
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# Tor tests transported along an equivalence of module categories

Let `X` and `X'` be ringed sites and let `e : Mod(𝒪_X) ≌ Mod(𝒪_{X'})` be an equivalence of the
categories of sheaves of modules which carries the ordinary tensor product of one to that of the
other, `e(M ⊗ N) ≅ e M ⊗ e N`, naturally in each variable.  For derived tensor product data `T`
on `X` and `T'` on `X'` — *arbitrary* ones, in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct` — and an object `E` of `D(𝒪_X)` which has a K-flat
representative, the cohomology sheaf `Hⁿ(E ⊗^L_T M[0])` vanishes exactly when
`Hⁿ(e E ⊗^L_{T'} (e M)[0])` does.  Consequently Tor amplitude in an interval is the same
condition on the two sides of `e`, and so is its restriction to any class of test modules which
`e` matches up.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_iff_of_equivalence`:
  **the Tor test at a module is the same on the two sides of `e`.**
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_iff_of_equivalence`: Tor
  amplitude in `[a, b]` is the same on the two sides of `e`.

## Implementation notes

Only the vanishing of a cohomology sheaf is transported, never an isomorphism of derived tensor
products, so no comparison of the two data `T` and `T'` is needed and none is made — the same
device as
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_hasTorAmplitude_derivedPullback`.
For a K-flat representative `K` of `E`, the left K-flat comparison field of `T` computes
`E ⊗^L_T M[0]` as the total complex `Tot(K ⊗ M[0])`; `e K` is K-flat
(`CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence`), so the same field of `T'` computes
`e E ⊗^L_{T'} (e M)[0]` as `Tot(e K ⊗ e(M[0]))`; and that total complex is `e Tot(K ⊗ M[0])`
(`CochainComplex.KFlatBifunctor.transportComplexIso`).  An equivalence is exact, so it commutes
with cohomology and reflects the zero object.

The K-flat representative is an argument rather than an instance of a resolution theorem, so the
statement holds at every universe shape of the two sites; a consumer supplies it from whichever
existence theorem applies to its site.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d u' v' w' d'

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [hDX : HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  {X' : RingedSite.{u', v', w'}}
  [HasSheafify X'.J AddCommGrpCat.{w'}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [hDX' : HasDerivedCategory.{d'} (RingedSite.Modules.{u', v', w'} X')]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} X'.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} X'.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u', v', w'} X') ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X'.O)
      (ComplexShape.up ℤ)]
  (e : RingedSite.Modules.{u, v, w} X ≌ RingedSite.Modules.{u', v', w'} X') [e.functor.Additive]
  (ε : ∀ a b : RingedSite.Modules.{u, v, w} X,
    e.functor.obj (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj a).obj b) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj (e.functor.obj a)).obj
        (e.functor.obj b))
  (hε₁ : ∀ {a a' : RingedSite.Modules.{u, v, w} X} (f : a ⟶ a') (b : RingedSite.Modules X),
    e.functor.map (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map f).app b) ≫
        (ε a' b).hom =
      (ε a b).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).map (e.functor.map f)).app
          (e.functor.obj b))
  (hε₂ : ∀ (a : RingedSite.Modules.{u, v, w} X) {b b' : RingedSite.Modules X} (g : b ⟶ b'),
    e.functor.map (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj a).map g) ≫
        (ε a b').hom =
      (ε a b).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj (e.functor.obj a)).map
          (e.functor.map g))

/-- The Tor test at `M` is the vanishing of the `n`-th cohomology of the total complex
`Tot(K ⊗ L)`, for a K-flat `K` representing `E` and `L` representing `M[0]`. -/
private theorem isZero_homology_tensor_single_iff_isZero_homology_mapBifunctor
    (T : DerivedTensorProduct.{u, v, w, d} X)
    (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ) (hK : IsKFlat X.O K)
    (E : RingedSite.DerivedModules.{u, v, w, d} X) (eK : DerivedCategory.Q.obj K ≅ E)
    (M : RingedSite.Modules.{u, v, w} X)
    (iM : (DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj M ≅
      DerivedCategory.Q.obj L) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) n).obj
        ((T.tensor.obj E).obj
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj M))) ↔
      IsZero ((HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)).homology n) :=
  (((DerivedCategory.homologyFunctor _ n).mapIso
        (((T.tensor.mapIso eK).app _).symm ≪≫ (T.tensor.obj (DerivedCategory.Q.obj K)).mapIso iM ≪≫
          T.comparisonLeft K L hK) ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app _).isZero_iff)

include ε hε₁ hε₂ in
/-- **The Tor test at a module is the same on the two sides of an equivalence of module
categories carrying the tensor product to the tensor product.**  Let `K` be a K-flat complex
representing `E`.  Then `Hⁿ(E ⊗^L_T M[0]) = 0` if and only if
`Hⁿ(e E ⊗^L_{T'} (e M)[0]) = 0`, for arbitrary derived tensor product data `T` and `T'`.

Both sides are the `n`-th cohomology of a total complex — `Tot(K ⊗ M[0])` and
`Tot(e K ⊗ e(M[0]))`, by the left K-flat comparisons of `T` and `T'` — and the second total
complex is `e` of the first. -/
theorem isZero_homology_tensor_single_iff_of_equivalence
    (T : DerivedTensorProduct.{u, v, w, d} X) (T' : DerivedTensorProduct.{u', v', w', d'} X')
    (K : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ) (hK : IsKFlat X.O K)
    (E : RingedSite.DerivedModules.{u, v, w, d} X) (eK : DerivedCategory.Q.obj K ≅ E)
    (M : RingedSite.Modules.{u, v, w} X) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) n).obj
        ((T.tensor.obj E).obj
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj M))) ↔
      IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u', v', w'} X') n).obj
        ((T'.tensor.obj (e.functor.mapDerivedCategory.obj E)).obj
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{u', v', w'} X') 0).obj
            (e.functor.obj M)))) := by
  have : e.inverse.Additive := e.inverse.additive_of_preserves_binary_products
  let := fun K L => CochainComplex.KFlatBifunctor.hasTotal_mapBicomplex_of_equivalence
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor X'.O) e ε hε₁ hε₂ K L
  set L := (HomologicalComplex.single (RingedSite.Modules.{u, v, w} X) (ComplexShape.up ℤ) 0).obj M
  set eC := e.functor.mapHomologicalComplex (ComplexShape.up ℤ)
  have hK' : IsKFlat X'.O (eC.obj K) :=
    CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor X'.O) e ε hε₁ hε₂ K hK
  have iT : e.functor.obj
        ((HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ)).homology n) ≅
      (HomologicalComplex.mapBifunctor (eC.obj K) (eC.obj L)
        (Stacks.SheafOfModules.Tensor.sheafTensor X'.O) (ComplexShape.up ℤ)).homology n :=
    ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso e.functor
        (ComplexShape.up ℤ) n).app _).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
        (CochainComplex.KFlatBifunctor.transportComplexIso
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (Stacks.SheafOfModules.Tensor.sheafTensor X'.O) e.functor e.functor e.functor
          ε hε₁ hε₂ K L)
  rw [isZero_homology_tensor_single_iff_isZero_homology_mapBifunctor T K L hK E eK M
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M) n,
    isZero_homology_tensor_single_iff_isZero_homology_mapBifunctor T' (eC.obj K) (eC.obj L) hK'
      _ ((e.functor.mapDerivedCategory.mapIso eK.symm ≪≫
        e.functor.mapDerivedCategoryFactors.app K).symm)
      (e.functor.obj M) ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (e.functor.obj M) ≪≫
        DerivedCategory.Q.mapIso
          ((HomologicalComplex.singleMapHomologicalComplex e.functor
            (ComplexShape.up ℤ) 0).app M).symm) n,
    ← iT.isZero_iff]
  exact ⟨e.functor.map_isZero, fun h => (e.inverse.map_isZero h).of_iso (e.unitIso.app _)⟩

include ε hε₁ hε₂ in
/-- **Tor amplitude in `[a, b]` is the same on the two sides of an equivalence of module
categories carrying the tensor product to the tensor product**, for arbitrary derived tensor
product data on the two sides and an object with a K-flat representative.

Every module on the target is `e` of a module on the source up to isomorphism, so the two
quantifiers range over the same tests by
`Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_iff_of_equivalence`. -/
theorem hasTorAmplitude_iff_of_equivalence
    (T : DerivedTensorProduct.{u, v, w, d} X) (T' : DerivedTensorProduct.{u', v', w', d'} X')
    (K : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ) (hK : IsKFlat X.O K)
    (E : RingedSite.DerivedModules.{u, v, w, d} X) (eK : DerivedCategory.Q.obj K ≅ E)
    (a b : ℤ) :
    HasTorAmplitude T E a b ↔ HasTorAmplitude T' (e.functor.mapDerivedCategory.obj E) a b := by
  constructor
  · intro h M' i hi
    refine ((isZero_homology_tensor_single_iff_of_equivalence e ε hε₁ hε₂ T T' K hK E eK
      (e.inverse.obj M') i).1 (h _ i hi)).of_iso ?_
    exact (DerivedCategory.homologyFunctor _ i).mapIso
      ((T'.tensor.obj _).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso (e.counitIso.app M'))).symm
  · intro h M i hi
    exact (isZero_homology_tensor_single_iff_of_equivalence e ε hε₁ hε₂ T T' K hK E eK
      M i).2 (h _ i hi)

/-- The cohomology sheaves of `e E` are `e` of the cohomology sheaves of `E`: an equivalence is
exact.  Stated with the two derived categories named, so that it applies when the two module
categories are one and the same category carrying two derived categories. -/
def homologyMapDerivedCategoryIso (E : RingedSite.DerivedModules.{u, v, w, d} X) (n : ℤ) :
    (DerivedCategory.homologyFunctor (RingedSite.Modules.{u', v', w'} X') n).obj
        (e.functor.mapDerivedCategory.obj E) ≅
      e.functor.obj ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) n).obj E) :=
  (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso e.functor n).app E

end Stacks.SheafOfModules.DerivedTensorProduct

end
