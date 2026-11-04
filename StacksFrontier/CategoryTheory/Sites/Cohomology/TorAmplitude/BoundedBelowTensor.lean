module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowFlatRepresentative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A lower Tor bound on one factor bounds the derived tensor product below

Let `(C, O)` be a ringed site, let `T` be a derived tensor product on `D(O)` in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct`, let `E` be an object of `D(O)` with Tor amplitude
in `[a, ∞]` and let `W` be an object of `D(O)` whose cohomology vanishes below `n`. Then the
cohomology of `E ⊗^L_O W` vanishes below `a + n`.

The bound is read on models. Tor amplitude in `[a, ∞]` is exactly a K-flat representative `P` of
`E` vanishing in every degree below `a` (Stacks 0F1M), and `W` has a representative `Z`
vanishing in every degree below `n`; a K-flat left factor computes the derived tensor product, so
`E ⊗^L_O W` is the class of the total tensor complex of `P` and `Z`, every summand `P^p ⊗_O Z^q`
of whose term in a degree below `a + n` has `p < a` or `q < n` and therefore vanishes.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isStrictlyGE_mapBifunctor`: the total tensor
  complex of two complexes vanishing below `a` and below `n` vanishes below `a + n`.
* `Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE`: the bound
  `a + n`.
* `Stacks.SheafOfModules.DerivedTensorProduct.isBoundedBelow_tensor_of_hasFiniteTorDimension`:
  the unquantified form, that a factor of finite Tor dimension tensored with a cohomologically
  bounded-below object is cohomologically bounded below.

## Implementation notes

Only `W` is required to be bounded below: the other factor carries a Tor bound instead, and no
cohomological bound on it is used or implied. This is the direction that is not
`Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor`, which bounds the tensor product above
from upper bounds on both factors, and it is not
`Stacks.Cohomology.TorAmplitude.Tensor.hasTorAmplitude_derivedTensor`, which assumes a Tor bound
on both factors and concludes one.

The three site universes are collapsed because Stacks 0F1M is: the K-flat representative with
flat terms it produces is built from the resolution of Stacks 06YS, which is available only at
the diagonal. The derived category's own hom universe stays independent.

## References

* [Stacks Project, Tag 0F1M](https://stacks.math.columbia.edu/tag/0F1M)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)] in
/-- The total tensor complex of two complexes vanishing below `a` and below `n` vanishes below
`a + n`. Every summand `P^p ⊗_O Z^q` of the term in a degree `i < a + n` has `p < a` or `q < n`,
so one factor vanishes and the summand vanishes with it. -/
theorem isStrictlyGE_mapBifunctor
    (P Z : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) (a n : ℤ)
    [CochainComplex.IsStrictlyGE P a] [CochainComplex.IsStrictlyGE Z n] :
    CochainComplex.IsStrictlyGE (HomologicalComplex.mapBifunctor P Z
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) (a + n) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (P.X p)).obj (Z.X q)) := by
    by_cases hp : p < a
    · exact ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map_isZero
        (P.isZero_of_isStrictlyGE a p hp)).obj _
    · exact ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (P.X p)).map_isZero
        (Z.isZero_of_isStrictlyGE n q (by dsimp at hpq; omega))
  exact hz.eq_of_src _ _

/-- A lower Tor bound on one factor and a lower cohomological bound on the other bound the
derived tensor product below: if `E` has Tor amplitude in `[a, ∞]` and the cohomology of `W`
vanishes below `n`, then the cohomology of `E ⊗^L_O W` vanishes below `a + n`. Nothing is assumed
about the cohomology of `E` beyond what the Tor bound gives. -/
@[sga "4 XVII 4.1.9" "(i)⇒(ii)"]
theorem isGE_tensor_of_hasTorAmplitudeGE (T : DerivedTensorProduct.{u, u, u, d} X)
    (E W : RingedSite.DerivedModules.{u, u, u, d} X) (a n : ℤ)
    (hE : HasTorAmplitudeGE T E a) (hW : W.IsGE n) :
    ((T.tensor.obj E).obj W).IsGE (a + n) := by
  obtain ⟨P, hPflat, -, hPzero, ⟨eP⟩⟩ :=
    (hasTorAmplitudeGE_iff_exists_kFlatRepresentative T E a).1 hE
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := W.exists_iso_Q_obj_of_isGE n
  have hPGE : CochainComplex.IsStrictlyGE P a := by
    rw [CochainComplex.isStrictlyGE_iff]; exact hPzero
  have hTot : (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P Z
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))).IsGE (a + n) := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    have := isStrictlyGE_mapBifunctor P Z a n
    infer_instance
  refine DerivedCategory.TStructure.t.isGE_of_iso (X := DerivedCategory.Q.obj
    (HomologicalComplex.mapBifunctor P Z
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) ?_ (a + n)
  exact (T.comparisonLeft P Z hPflat).symm ≪≫
    (T.tensor.mapIso eP).app (DerivedCategory.Q.obj Z) ≪≫
      ((T.tensor.obj E).mapIso eZ).symm

/-- A factor of finite Tor dimension tensored with a cohomologically bounded-below object is
cohomologically bounded below: the lower end of the Tor-amplitude interval of `E` shifts the
bound of `W`. -/
@[sga "6 I 5.3" "partial"]
theorem isBoundedBelow_tensor_of_hasFiniteTorDimension (T : DerivedTensorProduct.{u, u, u, d} X)
    (E W : RingedSite.DerivedModules.{u, u, u, d} X)
    (hE : HasFiniteTorDimension T E) (hW : DerivedCategoryB.IsBoundedBelow W) :
    DerivedCategoryB.IsBoundedBelow ((T.tensor.obj E).obj W) := by
  obtain ⟨a, b, hab⟩ := hE
  obtain ⟨n, hn⟩ := hW
  have hW' : W.IsGE n := (DerivedCategory.isGE_iff W n).mpr hn
  refine ⟨a + n, fun i hi => (DerivedCategory.isGE_iff _ (a + n)).1 ?_ i hi⟩
  exact isGE_tensor_of_hasTorAmplitudeGE T E W a n
    (hasTorAmplitudeGE_of_hasTorAmplitude T E a b hab) hW'

end Stacks.SheafOfModules.DerivedTensorProduct

end
