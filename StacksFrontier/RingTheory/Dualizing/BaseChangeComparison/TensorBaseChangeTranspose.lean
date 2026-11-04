module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeStrong

/-!
# Any equation in the lax monoidal structure map, with that map transposed away

`Dualizing.derivedTensorBaseChange` — the lax monoidal structure map `μ` of a model `F` of derived
extension of scalars along `f : R → A` — is invertible, with inverse
`Dualizing.derivedTensorBaseChangeSection`, and precomposition with that inverse is the composite
of four transposition bijections (`Dualizing.homEquiv_derivedTensorBaseChangeSection`).  Put
together, those two facts turn *any* equation of the shape

`μ_{X,Y} ≫ c = t`

into an equation in which `μ` does not occur, and in which the derived-Hom base-change morphism of
[stacks 0E1X] — the morphism `μ` is a double transpose of — does not occur either: transposing both
sides over [stacks 0GMT] leaves

`homEquiv_{0GMT} c = homEquiv_{0A63,R} (homEquiv_{0GMT} (homEquiv_{0A63,A}⁻¹ t) ≫ (0E1W)⁻¹)`,

whose only non-elementary factor is the inverse of the change-of-rings isomorphism
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso` of [stacks 0E1W].

Nothing is assumed of `X`, `Y`, `Z`, `c` or `t`: the statement is an `Iff`, both transpositions
used are bijections, and no K-flat representative is involved.

## Main results

* `Dualizing.derivedTensorBaseChange_comp_eq_iff` — the transposition: an equation
  `μ_{X,Y} ≫ c = t` holds exactly when the transposes of `c` and of `t` agree, the latter read
  backwards through [stacks 0E1W].

## Implementation notes

The proof is `Dualizing.homEquiv_derivedTensorBaseChangeSection` at `homEquiv⁻¹ t`, which says that
the right-hand side above is the transpose of `ν_{X,Y} ≫ t`, together with the two cancellation
identities `Dualizing.derivedTensorBaseChangeSection_comp_derivedTensorBaseChange` and
`Dualizing.derivedTensorBaseChange_comp_derivedTensorBaseChangeSection`; the transpose over
[stacks 0GMT] is injective, which is what turns the transposed equation back into the original one.

No `@[stacks]` attribute is placed here: this is a transposition, and covers no tag.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars

namespace Dualizing

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

/-- **An equation in the lax monoidal structure map, transposed.**  For morphisms
`c : F (X ⊗ᴸ_R Y) ⟶ Z` and `t : F X ⊗ᴸ_A F Y ⟶ Z`, the equation `μ_{X,Y} ≫ c = t` holds exactly
when the transpose of `c` over [stacks 0GMT] agrees with the transpose of `t` over [stacks 0A63]
at `A`, transposed over [stacks 0GMT] and read backwards through the change-of-rings isomorphism
of [stacks 0E1W].

Neither `μ` nor the derived-Hom base-change morphism of [stacks 0E1X] occurs on the right: the
isomorphism of [stacks 0E1W] is the only factor of either that survives the transposition.  This
is the shape in which an equation `μ ≫ c = t` becomes a question about [stacks 0E1W] alone. -/
theorem derivedTensorBaseChange_comp_eq_iff
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (c : F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
      (X, Y)) ⟶ Z)
    (t : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
      (F.obj X, F.obj Y) ⟶ Z) :
    derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ≫ c = t ↔
      (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv _ Z c =
        (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y _
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv X _
              (((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                  max uR uA uM + 1} A).homEquiv (F.obj X) (F.obj Y) Z).symm t) ≫
            (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
              comparison).inv.app (Opposite.op Y, Z)) := by
  have key := homEquiv_derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y Z
    (((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
      (F.obj X) (F.obj Y) Z).symm t)
  rw [AddEquiv.apply_symm_apply] at key
  rw [key, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · rintro rfl
    rw [← Category.assoc, derivedTensorBaseChangeSection_comp_derivedTensorBaseChange,
      Category.id_comp]
  · rintro rfl
    rw [← Category.assoc, derivedTensorBaseChange_comp_derivedTensorBaseChangeSection,
      Category.id_comp]

end Dualizing

end
