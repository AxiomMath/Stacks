module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionResolution
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMateFormula

/-!
# A chain-level value for the lax monoidal structure map of derived base change

`Dualizing.derivedTensorBaseChange` is presented as an adjoint transpose: by
`Dualizing.derivedTensorBaseChange_eq` it is

`μ_{X,Y} = homEquiv_A (F (coev) ≫ derivedHomBaseChange)`,

the transpose being taken under the tensor--Hom adjunction of [stacks 0A63] over `A`. The only
chain-level evaluation of that transpose used to be
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_homEquiv_apply`, which requires the target to
be `DerivedCategory.Q` of a **K-injective** complex. Here the target is
`F.obj (X ⊗ᴸ_R Y)`, a derived tensor product, about which nothing of the kind is known. So `μ`
had no chain-level value at the arguments at which it is needed.

`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_homEquiv_eq_model_general` removes that
restriction, and this file applies it: `μ` at arbitrary `(X, Y)` is the localization of a map of
complexes, read through the K-flat tensor model and three model isomorphisms.

## Main results

* `StacksDraft.DerivedHom.tensorHomUnit_eq_model`: the chain-level value of the coevaluation of
  [stacks 0A63], the first factor of the lax structure map. Its target is a derived tensor
  product, so this is the case the K-injective hypothesis used to exclude.
* `Dualizing.derivedTensorBaseChange_eq_model`: the chain-level value of the lax structure map.

## Implementation notes

The value is existential in the map of complexes `h`: it says that `μ` *is* a localized chain
map, not which one. So this is the value of `μ`, and not yet a comparison of `μ` with another
morphism.

The existential is avoidable, and a consumer that needs `μ` itself should not use this theorem.
`Dualizing.derivedTensorBaseChange_eq_evaluation` writes `μ` as the morphism of [stacks 0E1X]
tensored with an identity followed by an evaluation, with no existential and no chosen model, and
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_monoidalIso` values that
morphism with the degreewise monoidality isomorphism
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` --- the chain-level `μ` --- as its only
chain map.  The two together pin `μ` determinately, so the map `h` here is never needed.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor MonoidalCategory StacksDraft.DerivedHom

universe u v w

namespace StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

open CochainComplex HomComplex in
/-- **The coevaluation of [stacks 0A63] has a chain-level value.** The coevaluation
`K ⟶ RHom(L, K ⊗ᴸ L)` is by definition the inverse transpose of the identity of `K ⊗ᴸ L`, so its
target is a derived tensor product and `derivedHomAdjunctionOverRing_homEquiv_symm_apply` — which
needs a K-injective target — does not apply to it. Through a K-injective model `I` of the tensor
product it becomes the localization of the chain-level transpose of a map of complexes
`h : K ⊗ L ⟶ I`.

This is the first factor of the lax monoidal structure map of derived base change in
`Dualizing.derivedTensorBaseChange_eq`. -/
theorem tensorHomUnit_eq_model {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K L : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (hL : L.KFlat) :
    ∃ (I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (_ : I.IsKInjective)
      (φ : (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I) ≅
        (derivedHomAdjunctionOverRing.{u, v, w} R).tensor.obj
          ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K),
            (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L)))
      (h : K ⊗ L ⟶ I),
      (derivedHomAdjunctionOverRing.{u, v, w} R).tensorHomUnit
          ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
          ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L)) =
        (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map
              (Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} R) K L ≫
                Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} R) L (K ⊗ L) I h)) ≫
            (derivedHomModelIso.{u, v, w} R L I).inv ≫
          (derivedHomAdjunctionOverRing.{u, v, w} R).hom.map
            (show (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
                  (DerivedCategory.Q.obj L)),
                (derivedScalarEquivalence.{u, v, w} R).functor.obj
                  (DerivedCategory.Q.obj I)) ⟶
              (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
                  (DerivedCategory.Q.obj L)),
                (derivedHomAdjunctionOverRing.{u, v, w} R).tensor.obj
                  ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K),
                    (derivedScalarEquivalence.{u, v, w} R).functor.obj
                      (DerivedCategory.Q.obj L))) from
              (𝟙 (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
                  (DerivedCategory.Q.obj L))), φ.hom)) := by
  obtain ⟨I, hI, ⟨φ⟩⟩ := exists_isKInjective_model.{u, v, w} R
    ((derivedHomAdjunctionOverRing.{u, v, w} R).tensor.obj
      ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K),
        (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L)))
  have := hI
  obtain ⟨ψ, hψ⟩ := (derivedScalarEquivalence.{u, v, w} R).functor.map_surjective
    ((derivedTensorModelIso.{u, v, w} R K L hL).inv ≫ φ.inv)
  obtain ⟨h, rfl⟩ := exists_eq_Q_map_of_isKInjective (K ⊗ L) I ψ
  refine ⟨I, hI, φ, h, ?_⟩
  have hid : (derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
      (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h) ≫ φ.hom =
      𝟙 ((derivedHomAdjunctionOverRing.{u, v, w} R).tensor.obj
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K),
          (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L))) := by
    rw [hψ, Category.assoc, φ.inv_hom_id, Category.comp_id, Iso.hom_inv_id]
  have key := derivedHomAdjunctionOverRing_homEquiv_symm_apply_of_resolution.{u, v, w} K L I hL h
    _ φ
  rw [hid] at key
  exact key

end StacksDraft.DerivedHom

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

/-- **The lax monoidal structure map of derived base change has a chain-level value.** At every
pair of objects of `D(R)`, `Dualizing.derivedTensorBaseChange` is the localization of a map of
complexes `h : K ⊗ L ⟶ I` of `ULift A`-modules, with `L` K-flat and `I` a K-injective model of
the target, read through `StacksDraft.DerivedHom.derivedTensorModelIso` and the three model
isomorphisms. The equation is stated with the tensor bifunctor applied to the two source models on
the left rather than with its inverse on the right; that factor is an isomorphism, so this
determines `μ`.

This is `Dualizing.derivedTensorBaseChange_eq` followed by
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_homEquiv_eq_model_general`: no K-injectivity
is assumed of the target `F.obj (X ⊗ᴸ_R Y)`, which is a derived tensor product. -/
theorem derivedTensorBaseChange_eq_model
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    ∃ (K L I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (hL : L.KFlat)
      (α : (derivedScalarEquivalence.{uA, max uR uA uM, max uR uA uM + 1} A).functor.obj
        (DerivedCategory.Q.obj K) ≅ F.obj X)
      (β : (derivedScalarEquivalence.{uA, max uR uA uM, max uR uA uM + 1} A).functor.obj
        (DerivedCategory.Q.obj L) ≅ F.obj Y)
      (φ : (derivedScalarEquivalence.{uA, max uR uA uM, max uR uA uM + 1} A).functor.obj
          (DerivedCategory.Q.obj I) ≅
        F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.obj (X, Y)))
      (h : K ⊗ L ⟶ I),
      (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.map
            (show ((derivedScalarEquivalence.{uA, max uR uA uM, max uR uA uM + 1} A).functor.obj
                  (DerivedCategory.Q.obj K),
                (derivedScalarEquivalence.{uA, max uR uA uM, max uR uA uM + 1} A).functor.obj
                  (DerivedCategory.Q.obj L)) ⟶ (F.obj X, F.obj Y) from (α.hom, β.hom)) ≫
          derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y =
        (derivedTensorModelIso.{uA, max uR uA uM, max uR uA uM + 1} A K L hL).hom ≫
          (derivedScalarEquivalence.{uA, max uR uA uM, max uR uA uM + 1} A).functor.map
            (DerivedCategory.Q.map h) ≫ φ.hom := by
  obtain ⟨K, L, I, hL, α, β, φ, h, hval⟩ :=
    derivedHomAdjunctionOverRing_homEquiv_eq_model_general.{uA, max uR uA uM, max uR uA uM + 1}
      (F.obj X) (F.obj Y)
      (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
        max uR uA uM + 1} R).tensor.obj (X, Y)))
      (F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensorHomUnit X Y) ≫
        Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison Y
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y)))
  exact ⟨K, L, I, hL, α, β, φ, h,
    (congrArg _ (derivedTensorBaseChange_eq.{uR, uA, uM} f F comparison X Y)).trans hval⟩

end Dualizing

end
