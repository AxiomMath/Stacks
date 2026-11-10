module

public import StacksFrontier.Cotangent.RestrictedResolutionComparison

/-!
# The Tag 08SA sequence, functorial in the top algebra

For a tower `A → B → C` the short exact sequence whose triangle [Stacks, Tag 08SA] asserts is
`CommAlgCat.restrictedCotangentShortComplex` of
`StacksFrontier/Cotangent/StandardResolutionOverPolynomialBase.lean`,

`Ω[B⁄A] ⊗[B] C ⟶ Ω[P_•⁄A] ⊗[P_•] C ⟶ Ω[P_•⁄B] ⊗[P_•] C`,

for `P_•` the standard resolution of `C` over `B`. It is stated at one fixed top algebra `C`.
This file makes its middle term functorial in `C` and shows the two maps of the sequence commute
with that functoriality.

A `B`-algebra map `f : C ⟶ C'` induces `u : P_•(C/B) ⟶ P_•(C'/B)`, namely
`CommAlgCat.standardResolutionSquareMap` of the square `(𝟙_B, f)`
(`CommAlgCat.topSquareOfAlgHom`), and the induced map of differentials over `A` sends the pure
differential `1 ⊗ d p` to `1 ⊗ d (u p)`. That is the formula which pins the map down, and
everything here is proved from it.

## Main definitions

* `CommAlgCat.restrictedCotangentTopAdjoint` and `CommAlgCat.restrictedCotangentTopMap`: **the
  top-algebra functoriality map** `Ω[Pₙ⁄A] ⊗[Pₙ] C ⟶ Ω[P'ₙ⁄A] ⊗[P'ₙ] C'`, as the `Pₙ`-linear
  map adjoint to it and as the `C`-linear map itself, the target read over `C` along `f`.

## Main results

* `CommAlgCat.restrictedCotangentTopMap_D`: the map sends `1 ⊗ d p` to `1 ⊗ d (u p)`.
* `CommAlgCat.restrictedCotangentTopMap_naturality`: it is simplicial — it commutes with the
  structure maps `CommAlgCat.restrictedCotangentMap` of the two simplicial modules, so it is a
  morphism of simplicial `C`-modules `Ω[P_•⁄A] ⊗[P_•] C ⟶ Ω[P'_•⁄A] ⊗[P'_•] C'`.
* `CommAlgCat.restrictedCotangentTopMap_fromBase`: it commutes with the **first** map of the
  sequence, `CommAlgCat.restrictedCotangentFromBase`, the left-hand vertical being `f ⊗ 𝟙` on
  `C ⊗[B] Ω[B⁄A]`; stated on the pure elements `1 ⊗ d b`, which determine a map out of that base
  change (`ModuleCat.baseChange_kaehlerDifferential_hom_ext`).
* `CommAlgCat.restrictedCotangentTopMap_toRelative`: it commutes with the **second** map of the
  sequence, `CommAlgCat.restrictedCotangentToRelative`, the right-hand vertical being the
  functoriality of `L_{C/B}` in `C`, which is `CommAlgCat.squareCotangentTermMap` at the square
  `(𝟙_B, f)`.

## Implementation notes

The construction mirrors `CommAlgCat.restrictedCotangentMapAdjoint` and
`CommAlgCat.restrictedCotangentMap`, which are the same thing for a simplicial operator instead
of a map of top algebras: the `Pₙ`-linear map `ω ↦ 1 ⊗ Ω[u] ω` is written out and the `C`-linear
map is its adjoint under `ModuleCat.extendScalars ⊣ ModuleCat.restrictScalars`. The scalar towers
it needs are `A → Pₙ → P'ₙ`, which is
`CommAlgCat.standardResolutionSquareMap_algebraMap` composed with `A → B`, and
`Pₙ → P'ₙ → C'`, which is
`CommAlgCat.standardResolutionSquareMap_augmentation_app`: the augmentation of `P'_•` recovers
`f` after `u`.

The `A`-algebra structure on a term of the resolution is `Algebra.compHom` along `A → B`, the
same term as the `local instance` of
`StacksFrontier/Cotangent/StandardResolutionOverPolynomialBase.lean`; it is redeclared here because
that one is local to its file, and it is the only `Algebra A Pₙ` available, so no diamond
arises.

Every statement is at an arbitrary simplicial degree and an arbitrary `B`-algebra map; nothing is
evaluated at a concrete simplex.

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

/-- The `A`-algebra structure on a term of the standard resolution of a `B`-algebra over `B`,
given by the composite `A → B → Pₙ`. This is the `local instance` of
`StacksFrontier/Cotangent/StandardResolutionOverPolynomialBase.lean`, redeclared. -/
noncomputable local instance algebraStandardResolutionOverObj'
    {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
    {D : Type u} [CommRing D] [Algebra B D] (n : SimplexCategoryᵒᵖ) :
    Algebra A (standardResolutionOverObj.{u} B D n) :=
  Algebra.compHom _ (algebraMap A B)

/-- `A → B → Pₙ` is a scalar tower. -/
local instance isScalarTowerStandardResolutionOverObj'
    {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
    {D : Type u} [CommRing D] [Algebra B D] (n : SimplexCategoryᵒᵖ) :
    IsScalarTower A B (standardResolutionOverObj.{u} B D n) :=
  IsScalarTower.of_algebraMap_eq' rfl

section

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra B C] {C' : Type u} [CommRing C'] [Algebra B C']
  (f : C →ₐ[B] C') (n : SimplexCategoryᵒᵖ)

/-- **The map `u : Pₙ(C/B) ⟶ Pₙ(C'/B)` of standard resolutions induced by a `B`-algebra map.**
It is `CommAlgCat.standardResolutionSquareMap` of the square `(𝟙_B, f)`. -/
noncomputable abbrev topResolutionMap :
    standardResolutionOverObj.{u} B C n →+* standardResolutionOverObj.{u} B C' n :=
  standardResolutionSquareMap.{u, u, u} (topSquareOfAlgHom.{u} f) n

/-- `u` is compatible with the structure maps from `A`: it is so from `B`, and `A` acts
through `B`. -/
theorem topResolutionMap_algebraMap (a : A) :
    topResolutionMap f n (algebraMap A (standardResolutionOverObj.{u} B C n) a) =
      algebraMap A (standardResolutionOverObj.{u} B C' n) a :=
  standardResolutionSquareMap_algebraMap.{u, u, u} (topSquareOfAlgHom.{u} f) n (algebraMap A B a)

/-- The augmentation of `P_•(C'/B)` recovers `f` after `u`. -/
theorem topResolutionMap_aug (p : standardResolutionOverObj.{u} B C n) :
    standardResolutionOverAug B C' n (topResolutionMap f n p) =
      f (standardResolutionOverAug B C n p) :=
  standardResolutionSquareMap_augmentation_app.{u, u, u} (topSquareOfAlgHom.{u} f) n p

/-- The `Pₙ`-linear map `Ω[Pₙ⁄A] → C' ⊗[P'ₙ] Ω[P'ₙ⁄A]`, `ω ↦ 1 ⊗ Ω[u] ω`; it is adjoint to
`CommAlgCat.restrictedCotangentTopMap`. -/
noncomputable def restrictedCotangentTopAdjoint :
    ModuleCat.of (standardResolutionOverObj.{u} B C n)
        (KaehlerDifferential A (standardResolutionOverObj.{u} B C n)) ⟶
      (ModuleCat.restrictScalars (standardResolutionOverAug B C n)).obj
        ((ModuleCat.restrictScalars f.toRingHom).obj
          (restrictedCotangentTerm.{u, u} A B C' n)) := by
  let P := standardResolutionOverObj.{u} B C n
  let Q := standardResolutionOverObj.{u} B C' n
  let u := topResolutionMap f n
  letI : Algebra P Q := u.toAlgebra
  letI : Algebra Q C' := (standardResolutionOverAug B C' n).toAlgebra
  letI : Algebra P C' := ((standardResolutionOverAug B C' n).comp u).toAlgebra
  haveI : IsScalarTower A P Q :=
    IsScalarTower.of_algebraMap_eq fun a => (topResolutionMap_algebraMap f n a).symm
  haveI : IsScalarTower P Q C' := IsScalarTower.of_algebraMap_eq' rfl
  exact ModuleCat.ofHom
    (X := ModuleCat.of P (KaehlerDifferential A P))
    (Y := (ModuleCat.restrictScalars (standardResolutionOverAug B C n)).obj
      ((ModuleCat.restrictScalars f.toRingHom).obj (restrictedCotangentTerm.{u, u} A B C' n)))
    { toFun := fun x => (1 : C') ⊗ₜ[Q] (KaehlerDifferential.map A A P Q x)
      map_add' := fun x y => by
        change (TensorProduct.mk Q C' (KaehlerDifferential A Q) 1)
            (KaehlerDifferential.map A A P Q (x + y)) = _
        rw [map_add]
        exact (TensorProduct.mk Q C' (KaehlerDifferential A Q) 1).map_add _ _
      map_smul' := fun p x => by
        change (1 : C') ⊗ₜ[Q] (KaehlerDifferential.map A A P Q (p • x)) =
          f (standardResolutionOverAug B C n p) •
            ((1 : C') ⊗ₜ[Q] (KaehlerDifferential.map A A P Q x))
        rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        exact congrArg (fun c : C' => c ⊗ₜ[Q] (KaehlerDifferential.map A A P Q x))
          (congrArg (fun c : C' => c • (1 : C')) (topResolutionMap_aug f n p)) }

/-- **The top-algebra functoriality map** `Ω[Pₙ⁄A] ⊗[Pₙ] C ⟶ Ω[P'ₙ⁄A] ⊗[P'ₙ] C'`, the target read
over `C` along `f`: the `C`-linear extension of
`CommAlgCat.restrictedCotangentTopAdjoint`. -/
noncomputable def restrictedCotangentTopMap :
    restrictedCotangentTerm.{u, u} A B C n ⟶
      (ModuleCat.restrictScalars f.toRingHom).obj (restrictedCotangentTerm.{u, u} A B C' n) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (standardResolutionOverAug B C n) (restrictedCotangentTopAdjoint f n)

/-- **The formula which pins the top-algebra functoriality map:** it sends the pure differential
`1 ⊗ d p` to `1 ⊗ d (u p)`. -/
@[simp]
theorem restrictedCotangentTopMap_D (p : standardResolutionOverObj.{u} B C n) :
    restrictedCotangentTopMap f n (restrictedCotangentDifferential.{u, u} A B C n p) =
      restrictedCotangentDifferential.{u, u} A B C' n (topResolutionMap f n p) := by
  have key : restrictedCotangentTopMap f n
        (restrictedCotangentDifferential.{u, u} A B C n p) =
      (1 : C) • (restrictedCotangentTopAdjoint f n)
        (KaehlerDifferential.D A (standardResolutionOverObj.{u} B C n) p) :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
      (standardResolutionOverAug B C n) (restrictedCotangentTopAdjoint f n) (1 : C)
      (KaehlerDifferential.D A (standardResolutionOverObj.{u} B C n) p)
  rw [key, one_smul]
  let P := standardResolutionOverObj.{u} B C n
  let Q := standardResolutionOverObj.{u} B C' n
  let u := topResolutionMap f n
  let : Algebra P Q := u.toAlgebra
  let : Algebra Q C' := (standardResolutionOverAug B C' n).toAlgebra
  let : Algebra P C' := ((standardResolutionOverAug B C' n).comp u).toAlgebra
  have : IsScalarTower A P Q :=
    IsScalarTower.of_algebraMap_eq fun a => (topResolutionMap_algebraMap f n a).symm
  have : IsScalarTower P Q C' := IsScalarTower.of_algebraMap_eq' rfl
  change (1 : C') ⊗ₜ[Q] (KaehlerDifferential.map A A P Q
      (KaehlerDifferential.D A P p)) = _
  rw [KaehlerDifferential.map_D]
  rfl

/-! ### The functoriality is simplicial, and commutes with the two maps of the sequence -/

/-- **The top-algebra functoriality map is simplicial.** It commutes with the structure maps of
the two simplicial `C`-modules, because `CommAlgCat.standardResolutionSquareMap` commutes with
every simplicial operator. -/
theorem restrictedCotangentTopMap_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    restrictedCotangentMap.{u, u} A B C g ≫ restrictedCotangentTopMap f j =
      restrictedCotangentTopMap f i ≫
        (ModuleCat.restrictScalars f.toRingHom).map
          (restrictedCotangentMap.{u, u} A B C' g) := by
  refine restrictedCotangentTerm_hom_ext.{u, u} A B C i _ _ fun p => ?_
  change restrictedCotangentTopMap f j (restrictedCotangentMap.{u, u} A B C g
      (restrictedCotangentDifferential.{u, u} A B C i p)) =
    restrictedCotangentMap.{u, u} A B C' g (restrictedCotangentTopMap f i
      (restrictedCotangentDifferential.{u, u} A B C i p))
  rw [restrictedCotangentMap_D, restrictedCotangentTopMap_D, restrictedCotangentTopMap_D,
    restrictedCotangentMap_D]
  exact congrArg (restrictedCotangentDifferential.{u, u} A B C' j)
    (standardResolutionSquareMap_naturality.{u, u, u} (topSquareOfAlgHom.{u} f) g p)

/-- **The top-algebra functoriality map commutes with the first map of the sequence.** On the
pure element `1 ⊗ d b` of `C ⊗[B] Ω[B⁄A]` both composites give the pure differential of the image
of `b`: the comparison of resolutions is a `B`-algebra map, so it carries `algebraMap B Pₙ b` to
`algebraMap B P'ₙ b`. -/
theorem restrictedCotangentTopMap_fromBase (b : B) :
    restrictedCotangentTopMap f n (restrictedCotangentFromBase.{u, u} A B C n
        ((1 : C) ⊗ₜ[B] KaehlerDifferential.D A B b)) =
      restrictedCotangentFromBase.{u, u} A B C' n
        ((1 : C') ⊗ₜ[B] KaehlerDifferential.D A B b) := by
  rw [restrictedCotangentFromBase_D, restrictedCotangentTopMap_D,
    restrictedCotangentFromBase_D]
  exact congrArg (restrictedCotangentDifferential.{u, u} A B C' n)
    (standardResolutionSquareMap_algebraMap.{u, u, u} (topSquareOfAlgHom.{u} f) n b)

/-- **The top-algebra functoriality map commutes with the second map of the sequence**, the
right-hand vertical being the functoriality of `L_{C/B}` in `C` — the map of [Stacks, Tag 08PN]
at the square `(𝟙_B, f)`. Both composites send `1 ⊗ d p` to `1 ⊗ d (u p)`. -/
theorem restrictedCotangentTopMap_toRelative :
    restrictedCotangentToRelative.{u, u} A B C n ≫
        squareCotangentTermMap.{u, u, u} (topSquareOfAlgHom.{u} f) n =
      restrictedCotangentTopMap f n ≫
        (ModuleCat.restrictScalars f.toRingHom).map
          (restrictedCotangentToRelative.{u, u} A B C' n) := by
  refine restrictedCotangentTerm_hom_ext.{u, u} A B C n _ _ fun p => ?_
  change squareCotangentTermMap.{u, u, u} (topSquareOfAlgHom.{u} f) n
      (restrictedCotangentToRelative.{u, u} A B C n
        (restrictedCotangentDifferential.{u, u} A B C n p)) =
    restrictedCotangentToRelative.{u, u} A B C' n (restrictedCotangentTopMap f n
      (restrictedCotangentDifferential.{u, u} A B C n p))
  rw [restrictedCotangentToRelative_D, squareCotangentTermMap_D, restrictedCotangentTopMap_D,
    restrictedCotangentToRelative_D]


end

end CommAlgCat

end
