module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionTensorPrefix
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorCovariantKFlatLift

/-!
# The [stacks 068I] candidate's transpose at a K-flat pair

`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` values the [stacks 068I] candidate `μ'` at a pair of
localizations of K-flat complexes, but only after one trailing isomorphism: what it pins is
`μ' ≫ F(tensor comparison) ≫ (model comparison)`, the two factors that identify
`F (Q K ⊗ᴸ_R Q L)` with the class of the degreewise base change of the total tensor complex.  That
composite is `Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso`, an isomorphism, so the value
of `μ'` itself follows.

The keystone does not use `μ'` directly, though: by
`Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftTranspose` it enters through its [stacks 0A63]
transpose over `A`, restricted to `R` and then lifted.  This file performs the first of those
three steps, which is the only one with content: transposing a composite whose second factor is a
morphism of the *target* is naturality of the transpose in the target variable, so the transpose
of `μ'` is the transpose of the pinned value followed by the internal Hom of the inverse of that
isomorphism.

**What is not done here.**  Nothing is registered and no caveat is lifted.  The [stacks 068I]
identification stays open, and so does the companion hypothesis `h` of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor`, whose frontier is
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `Dualizing.tensorBaseChangeMor_transpose_eq_q_obj` -- the [stacks 0A63] transpose over `A` of
  the [stacks 068I] candidate at a pair of localizations of K-flat complexes: the transpose of the
  tensor of the two model comparisons followed by the K-flat comparison over `A` and the ordinary
  tensor base-change isomorphism of total complexes, followed by the internal Hom of the inverse
  of `Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso`.

## Implementation notes

The transposition step is
`StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_symm_naturality_right`, applied in term
position after one `congrArg` with a hand-written motive: the equation being substituted is an
equation of the candidate itself, so no keyed matching is involved.  The identity of the trailing
isomorphism's `hom` with the two factors `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` writes out
is `Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso_hom`, which holds by `rfl`, so the pinned
equation is used at the isomorphism's own spelling with no rewriting.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA} f)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **The [stacks 0A63] transpose over `A` of the [stacks 068I] candidate, at a pair of
localizations of K-flat complexes.**

`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` pins the candidate only after the isomorphism
`Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso` that identifies `F (Q K ⊗ᴸ_R Q L)` with
the class of the degreewise base change of the total tensor complex.  The [stacks 0A63] transpose
over `A` turns that trailing isomorphism into the internal Hom of its inverse, by naturality of the
transpose in its target variable, and leaves the pinned value under one transpose.

This is the shape in which the candidate enters the keystone: by
`Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftTranspose` the equation to be checked begins with
`E.functor` of the restriction to `R` of exactly this transpose, preceded by the unit of
[stacks 0GMT] at `Q K`. -/
theorem tensorBaseChangeMor_transpose_eq_q_obj
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    let dA := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
      max uR uA uM + 1} A
    let W := (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)
    ∃ (hFL : IsKFlat.{uA, max uR uA uM}
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L))
        (e : tensorComplex.{uA, max uR uA uM}
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) ≅
          (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
            (tensorComplex.{uR, max uR uA uM} K L)),
      IsTensorBaseChangeIso.{uR, uA, max uR uA uM} f K L e ∧
        (dA.homEquiv (F.obj (DerivedCategory.Q.obj K)) (F.obj (DerivedCategory.Q.obj L))
              (F.obj W)).symm
            (tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
              (DerivedCategory.Q.obj L)) =
          (dA.homEquiv (F.obj (DerivedCategory.Q.obj K)) (F.obj (DerivedCategory.Q.obj L))
                (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
                  (tensorComplex.{uR, max uR uA uM} K L)))).symm
              (dA.tensor.map
                    ((CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
                        ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
                          DerivedCategory (ModuleCat.{max uR uA uM} A) ×
                            DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
                        (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                            max uR uA uM} f).obj K),
                          DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                            max uR uA uM} f).obj L)))) ≫
                  (derivedTensor_comparison.{uA, max uR uA uM} A
                      ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
                      ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFL).hom ≫
                    DerivedCategory.Q.map e.hom) ≫
            dA.hom.map (𝟙 (Opposite.op (F.obj (DerivedCategory.Q.obj L))),
              (_root_.Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uA, uM} f F
                comparison K L hK hL).inv) := by
  intro dA W
  obtain ⟨hFL, e, he, heq⟩ :=
    tensorBaseChangeMor_comp_eq_q_obj.{uR, uA, uM} f D F comparison K L hK hL
  refine ⟨hFL, e, he, ?_⟩
  exact (congrArg (fun z => (dA.homEquiv (F.obj (DerivedCategory.Q.obj K))
      (F.obj (DerivedCategory.Q.obj L)) (F.obj W)).symm z)
      ((Iso.eq_comp_inv (_root_.Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uA, uM}
        f F comparison K L hK hL)).mpr heq)).trans
    (dA.homEquiv_symm_naturality_right _ _)

end Dualizing

end
