module

public import StacksFrontier.Cotangent.RestrictedCotangentTopFunctoriality

/-!
# The Tag 08SA sequence as a short complex functorial in the top algebra

`CommAlgCat.restrictedCotangentShortComplex` of
`StacksFrontier/Cotangent/StandardResolutionOverPolynomialBase.lean` is the short complex of
simplicial `C`-modules

`C ⊗[B] Ω[B⁄A] ⟶ Ω[P_•⁄A] ⊗[P_•] C ⟶ Ω[P_•⁄B] ⊗[P_•] C`

whose triangle [Stacks, Tag 08SA] asserts, for `P_•` the standard resolution of `C` over `B`. It
is stated at one fixed top algebra.
`StacksFrontier/Cotangent/RestrictedCotangentTopFunctoriality.lean` makes its middle term functorial
in `C` and proves that both of its maps commute with that functoriality. This file assembles
those results into a single **morphism of short complexes**, which is the shape the five lemma
takes: `quasiIso_τ₂_of_shortExact` of
`StacksFrontier/Algebra/DifferentialGraded/Module/AdmissibleQuasiIso.lean` concludes that the middle
component of a morphism of short exact sequences of cochain complexes is a quasi-isomorphism from
the outer two.

## Main definitions

* `CommAlgCat.baseDifferentialsCancelIso`: cancellation of base change,
  `C' ⊗[C] (C ⊗[B] Ω[B⁄A]) ≅ C' ⊗[B] Ω[B⁄A]`.
* `CommAlgCat.baseDifferentialsTopMap`: the first component, `f ⊗ 𝟙` on `C ⊗[B] Ω[B⁄A]`.
* `CommAlgCat.restrictedCotangentShortComplexTopMap`: **the morphism of short complexes of
  simplicial modules** induced by a `B`-algebra map `f : C ⟶ C'`, the target read over `C`
  along `f`.

## Main results

* `CommAlgCat.baseDifferentialsTopMap_tmul`: the first component sends `c ⊗ ω` to `f c ⊗ ω`.
* `CommAlgCat.extendScalars_baseDifferentialsTopMap_counit`: **its adjoint is the cancellation
  isomorphism**, hence an isomorphism. This is what makes the first vertical of the five-lemma
  diagram invertible after base change along `f`, with no hypothesis on `Ω[B⁄A]`.
* `CommAlgCat.restrictedCotangentShortComplexTopMap_τ₁`,
  `CommAlgCat.restrictedCotangentShortComplexTopMap_τ₂` and
  `CommAlgCat.restrictedCotangentShortComplexTopMap_τ₃`: the three components are
  `CommAlgCat.baseDifferentialsTopMap`, `CommAlgCat.restrictedCotangentTopMap` and
  `CommAlgCat.squareCotangentSimplicialMap` at the square `(𝟙_B, f)`.

## Implementation notes

The first component is *defined* as the adjoint of the cancellation isomorphism under
`ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f`. Writing it that way rather than as an
explicit `C`-linear map has two advantages: no `Module C (C' ⊗[B] Ω[B⁄A])` instance has to be
introduced for its statement, the adjunction supplying the semilinearity; and the fact the five
lemma needs — that extension of scalars of it, followed by the counit, is invertible — is the
adjunction's own triangle identity rather than a computation.

The remaining two components and the two commutation squares are the four results of
`StacksFrontier/Cotangent/RestrictedCotangentTopFunctoriality.lean`. The first square is stated
there on the pure elements `1 ⊗ d b`, which determine a map out of `C ⊗[B] Ω[B⁄A]`
(`ModuleCat.baseChange_kaehlerDifferential_hom_ext`), so it is obtained from that extensionality
and not by a separate computation.

The first term of the short complex is a *constant* simplicial module, so its component of the
morphism is a natural transformation between constant functors and its naturality is the unit
law.

Everything is at an arbitrary `B`-algebra map and an arbitrary simplicial degree.

## References

* [Stacks Project, Tag 031K](https://stacks.math.columbia.edu/tag/031K)
* [Stacks Project, Tag 08SA](https://stacks.math.columbia.edu/tag/08SA)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology
open scoped TensorProduct

universe u

namespace CommAlgCat

section

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra B C] {C' : Type u} [CommRing C'] [Algebra B C']
  (f : C →ₐ[B] C')

/-- **Cancellation of base change on the differentials of the middle ring:**
`C' ⊗[C] (C ⊗[B] Ω[B⁄A]) ≅ C' ⊗[B] Ω[B⁄A]`, the source read as extension of scalars along `f`. -/
noncomputable def baseDifferentialsCancelIso :
    (ModuleCat.extendScalars f.toRingHom).obj
        (ModuleCat.of C (C ⊗[B] KaehlerDifferential A B)) ≅
      ModuleCat.of C' (C' ⊗[B] KaehlerDifferential A B) :=
  letI : Algebra C C' := f.toRingHom.toAlgebra
  haveI : IsScalarTower B C C' :=
    IsScalarTower.of_algebraMap_eq fun b => (f.commutes b).symm
  (TensorProduct.AlgebraTensorModule.cancelBaseChange B C C' C'
    (KaehlerDifferential A B)).toModuleIso

/-- **The first component of the morphism of short complexes:** `f ⊗ 𝟙` on `C ⊗[B] Ω[B⁄A]`, the
target read over `C` along `f`. It is the adjoint of `CommAlgCat.baseDifferentialsCancelIso`
under `ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f`. -/
noncomputable def baseDifferentialsTopMap :
    ModuleCat.of C (C ⊗[B] KaehlerDifferential A B) ⟶
      (ModuleCat.restrictScalars f.toRingHom).obj
        (ModuleCat.of C' (C' ⊗[B] KaehlerDifferential A B)) :=
  (ModuleCat.extendRestrictScalarsAdj f.toRingHom).homEquiv
    (ModuleCat.of C (C ⊗[B] KaehlerDifferential A B))
    (ModuleCat.of C' (C' ⊗[B] KaehlerDifferential A B))
    (baseDifferentialsCancelIso (A := A) f).hom

/-- The first component sends `c ⊗ ω` to `f c ⊗ ω`. -/
@[simp]
theorem baseDifferentialsTopMap_tmul (c : C) (ω : KaehlerDifferential A B) :
    baseDifferentialsTopMap (A := A) f (c ⊗ₜ[B] ω) = f c ⊗ₜ[B] ω := by
  let : Algebra C C' := f.toRingHom.toAlgebra
  have : IsScalarTower B C C' :=
    IsScalarTower.of_algebraMap_eq fun b => (f.commutes b).symm
  show (f c * (1 : C')) ⊗ₜ[B] ω = f c ⊗ₜ[B] ω
  rw [mul_one]

/-- **The adjoint of the first component is the cancellation isomorphism**, so it is invertible.
This is the triangle identity of the adjunction, the component being defined as the adjoint. -/
theorem extendScalars_baseDifferentialsTopMap_counit :
    (ModuleCat.extendScalars f.toRingHom).map (baseDifferentialsTopMap (A := A) f) ≫
        (ModuleCat.extendRestrictScalarsAdj f.toRingHom).counit.app
          (ModuleCat.of C' (C' ⊗[B] KaehlerDifferential A B)) =
      (baseDifferentialsCancelIso (A := A) f).hom :=
  ((ModuleCat.extendRestrictScalarsAdj f.toRingHom).homEquiv
    (ModuleCat.of C (C ⊗[B] KaehlerDifferential A B))
    (ModuleCat.of C' (C' ⊗[B] KaehlerDifferential A B))).symm_apply_apply
      (baseDifferentialsCancelIso (A := A) f).hom

/-- The first vertical of the five-lemma diagram is an isomorphism. -/
theorem isIso_extendScalars_baseDifferentialsTopMap_counit :
    IsIso ((ModuleCat.extendScalars f.toRingHom).map (baseDifferentialsTopMap (A := A) f) ≫
      (ModuleCat.extendRestrictScalarsAdj f.toRingHom).counit.app
        (ModuleCat.of C' (C' ⊗[B] KaehlerDifferential A B))) := by
  rw [extendScalars_baseDifferentialsTopMap_counit]
  infer_instance

/-- **The morphism of short complexes of simplicial modules** induced by a `B`-algebra map
`f : C ⟶ C'`, the target read over `C` along `f`. Its three components are `f ⊗ 𝟙` on
`C ⊗[B] Ω[B⁄A]`, `CommAlgCat.restrictedCotangentTopMap`, and
`CommAlgCat.squareCotangentSimplicialMap` at the square `(𝟙_B, f)`; the two commutation squares
are `CommAlgCat.restrictedCotangentTopMap_fromBase` and
`CommAlgCat.restrictedCotangentTopMap_toRelative`. -/
noncomputable def restrictedCotangentShortComplexTopMap :
    restrictedCotangentShortComplex.{u, u} A B C ⟶
      (restrictedCotangentShortComplex.{u, u} A B C').map
        ((SimplicialObject.whiskering (ModuleCat.{u} C') (ModuleCat.{u} C)).obj
          (ModuleCat.restrictScalars f.toRingHom)) where
  τ₁ :=
    { app := fun _ => baseDifferentialsTopMap (A := A) f
      naturality := fun _ _ _ => by
        change 𝟙 (ModuleCat.of C (C ⊗[B] KaehlerDifferential A B)) ≫
            baseDifferentialsTopMap (A := A) f =
          baseDifferentialsTopMap (A := A) f ≫ (ModuleCat.restrictScalars f.toRingHom).map
            (𝟙 (ModuleCat.of C' (C' ⊗[B] KaehlerDifferential A B)))
        rw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id] }
  τ₂ :=
    { app := fun n => restrictedCotangentTopMap f n
      naturality := fun _ _ g => restrictedCotangentTopMap_naturality f g }
  τ₃ := squareCotangentSimplicialMap.{u, u, u} (topSquareOfAlgHom.{u} f)
  comm₁₂ := by
    refine NatTrans.ext (funext fun n => ?_)
    change baseDifferentialsTopMap (A := A) f ≫ (ModuleCat.restrictScalars f.toRingHom).map
          (restrictedCotangentFromBase.{u, u} A B C' n) =
      restrictedCotangentFromBase.{u, u} A B C n ≫ restrictedCotangentTopMap f n
    refine ModuleCat.baseChange_kaehlerDifferential_hom_ext (A := A) (R := B) _ _ fun b => ?_
    change restrictedCotangentFromBase.{u, u} A B C' n
        (baseDifferentialsTopMap (A := A) f
          ((1 : C) ⊗ₜ[B] KaehlerDifferential.D A B b)) =
      restrictedCotangentTopMap f n (restrictedCotangentFromBase.{u, u} A B C n
        ((1 : C) ⊗ₜ[B] KaehlerDifferential.D A B b))
    rw [baseDifferentialsTopMap_tmul, map_one, restrictedCotangentTopMap_fromBase]
  comm₂₃ := by
    refine NatTrans.ext (funext fun n => ?_)
    exact (restrictedCotangentTopMap_toRelative (A := A) f n).symm

/-- The first component of the morphism of short complexes is `f ⊗ 𝟙`. -/
@[simp]
theorem restrictedCotangentShortComplexTopMap_τ₁ (n : SimplexCategoryᵒᵖ) :
    (restrictedCotangentShortComplexTopMap (A := A) f).τ₁.app n =
      baseDifferentialsTopMap (A := A) f := rfl

/-- The middle component of the morphism of short complexes is the top-algebra functoriality
map. -/
@[simp]
theorem restrictedCotangentShortComplexTopMap_τ₂ (n : SimplexCategoryᵒᵖ) :
    (restrictedCotangentShortComplexTopMap (A := A) f).τ₂.app n =
      restrictedCotangentTopMap f n := rfl

/-- The last component of the morphism of short complexes is the functoriality of `L_{C/B}` in
`C`, the map of [Stacks, Tag 08PN] at the square `(𝟙_B, f)`. -/
@[simp]
theorem restrictedCotangentShortComplexTopMap_τ₃ :
    (restrictedCotangentShortComplexTopMap (A := A) f).τ₃ =
      squareCotangentSimplicialMap.{u, u, u} (topSquareOfAlgHom.{u} f) := rfl

end

end CommAlgCat

end
