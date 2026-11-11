module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Cotangent.BaseChangeCompositionIterated
public import StacksFrontier.Cotangent.ProductDecompositionSndComponent
public import StacksFrontier.Cotangent.Triangle.DisplayedTriangle
public import StacksFrontier.Cotangent.Triangle.VanishingVertex

/-!
# The fundamental triangle for arbitrary ring maps, by descent from `B × C`

For ring maps `A → B → C` with `B → C` injective,
`CommAlgCat.fundamentalTriangle_distinguished` of
`StacksFrontier/Cotangent/Triangle/DisplayedTriangle.lean` proves that the display of
[Stacks, Tag 08QS] is a distinguished triangle in `D(C)`. This file removes the injectivity.

The route is the one [Stacks, Remark 08SD] prescribes. The map `B ⟶ B × C`, `b ↦ (b, f b)`, is
injective — the first projection is a retraction — so the tower `A → B → B × C` has the triangle
already. Base change along the second projection `B × C → C` is exact, that projection being
flat, so it carries the triangle to a distinguished triangle in `D(C)`; and the three vertices
come out as the display's own, because

* `L_{B/A} ⊗^𝐋_B (B × C) ⊗_{B × C} C = L_{B/A} ⊗^𝐋_B C` is the cancellation of two base changes,
* `L_{B×C/A} ⊗_{B × C} C = L_{C/A}` and `L_{B×C/B} ⊗_{B × C} C = L_{C/B}` are the second
  component of [Stacks, Tag 08SC] over the bases `A` and `B`.

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategoryFactors_hom_app_comp`: the comparison between the
  derived and the degreewise image of a complex is natural, in the shape the three
  identifications below consume.
* `CommAlgCat.prodSndBaseMap` and `CommAlgCat.prodSndTopMap`: the chain-level maps
  `L_{B×C/A} ⊗_{B×C} C ⟶ L_{C/A}` and `L_{B×C/B} ⊗_{B×C} C ⟶ L_{C/B}`.
* `CommAlgCat.descentIso₁`, `CommAlgCat.descentIso₂`, `CommAlgCat.descentIso₃`: the three
  identifications of the base-changed vertices with the display's own.
* `CommAlgCat.productFundamentalMor₃`: **the third displayed morphism**
  `L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)⟦1⟧`, for arbitrary ring maps `A → B → C`.

## Main results

* `CommAlgCat.productDisplayMor₁_eq_fundamentalMor₁` and
  `CommAlgCat.productDisplayMor₂_eq_fundamentalMor₂`: the first two morphisms of the descended
  triangle, read between the display's own vertices, **are** the display's own
  `CommAlgCat.fundamentalMor₁` and `CommAlgCat.fundamentalMor₂`.
* `CommAlgCat.productFundamentalTriangle_distinguished`: **[Stacks, Tag 08QX] for arbitrary ring
  maps**, which is also the distinguishedness clause of the display of [Stacks, Tag 08QS].
* `CommAlgCat.exists_distTriang_fundamentalVertex`: the same, in existential form.
* `CommAlgCat.isIso_fundamentalMor₁_of_isZero_fundamentalVertex₃` and
  `CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero_fundamentalVertex₃`:
  **[Stacks, Tag 08R3] for arbitrary ring maps**, read off that triangle by the vanishing step
  of `StacksFrontier/Cotangent/Triangle/VanishingVertex.lean`.

## References

* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 08R3](https://stacks.math.columbia.edu/tag/08R3)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CategoryTheory.Functor

section DerivedFactors

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The derived and the degreewise base change agree on a composite.** The image under
`CategoryTheory.Functor.mapDerivedCategory` of the localization of a map of complexes, followed by
the comparison `CategoryTheory.Functor.mapDerivedCategoryFactors` and the localization of a map out
of the degreewise image, is the comparison followed by the localization of the degreewise
composite. This is the naturality of the comparison. -/
theorem mapDerivedCategoryFactors_hom_app_comp {X Y : CochainComplex C₁ ℤ}
    {Y' : CochainComplex C₂ ℤ} (g : X ⟶ Y)
    (ψ : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ⟶ Y') :
    F.mapDerivedCategory.map (DerivedCategory.Q.map g) ≫
        F.mapDerivedCategoryFactors.hom.app Y ≫ DerivedCategory.Q.map ψ =
      F.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g ≫ ψ) := by
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc,
    F.mapDerivedCategoryFactors_hom_naturality g]

end DerivedFactors

end CategoryTheory.Functor

namespace CommAlgCat

section Flat

variable (B C : Type u) [CommRing B] [CommRing C]

/-- Base change along the second projection of a product ring preserves finite limits: the
projection is flat. -/
instance preservesFiniteLimits_extendScalars_snd :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)) :=
  extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ (RingHom.flat_snd B C)

end Flat

attribute [local instance] HasDerivedCategory.standard

section Tower

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- **`B ⟶ B × C`, `b ↦ (b, f b)`, is injective**: the first projection is a retraction. This is
the split injection of [Stacks, Remark 08SD]. -/
theorem injective_algebraMap_prod : Function.Injective (algebraMap B (B × C)) :=
  fun _ _ h => congrArg Prod.fst h

/-- The chain-level map `L_{B×C/A} ⊗_{B×C} C ⟶ L_{C/A}`: the second component of
[Stacks, Tag 08SC] over the base `A`, in the adjoint shape. -/
def prodSndBaseMap :
    (((ModuleCat.extendScalars (RingHom.snd B C)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A (CommAlgCat.of A (B × C)))) ⟶
      cotangentComplex.{u, u} A (CommAlgCat.of A C) :=
  ((ModuleCat.extendScalars (RingHom.snd B C)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (squareCotangentComplexMap.{u, u, u}
        (productSndSquare.{u, u} A (CommAlgCat.of A B) (CommAlgCat.of A C))) ≫
    ModuleCat.extendRestrictScalarsAdjCounitComplex (RingHom.snd B C) (ComplexShape.up ℤ)
      (cotangentComplex.{u, u} A (CommAlgCat.of A C))

/-- The chain-level map `L_{B×C/B} ⊗_{B×C} C ⟶ L_{C/B}`: the second component of
[Stacks, Tag 08SC] over the base `B`, in the adjoint shape. -/
def prodSndTopMap :
    (((ModuleCat.extendScalars (RingHom.snd B C)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} B (CommAlgCat.of B (B × C)))) ⟶
      cotangentComplex.{u, u} B (CommAlgCat.of B C) :=
  ((ModuleCat.extendScalars (RingHom.snd B C)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (squareCotangentComplexMap.{u, u, u}
        (productSndSquare.{u, u} B (CommAlgCat.of B B) (CommAlgCat.of B C))) ≫
    ModuleCat.extendRestrictScalarsAdjCounitComplex (RingHom.snd B C) (ComplexShape.up ℤ)
      (cotangentComplex.{u, u} B (CommAlgCat.of B C))

omit [Algebra B C] [IsScalarTower A B C] in
/-- `CommAlgCat.prodSndBaseMap` is a quasi-isomorphism: this is the second component of
[Stacks, Tag 08SC] over the base `A`. -/
theorem quasiIso_prodSndBaseMap : QuasiIso (prodSndBaseMap A B C) :=
  quasiIso_cotangentExtendScalars_productSnd A (CommAlgCat.of A B) (CommAlgCat.of A C)

/-- `CommAlgCat.prodSndTopMap` is a quasi-isomorphism: this is the second component of
[Stacks, Tag 08SC] over the base `B`. -/
theorem quasiIso_prodSndTopMap : QuasiIso (prodSndTopMap B C) :=
  quasiIso_cotangentExtendScalars_productSnd B (CommAlgCat.of B B) (CommAlgCat.of B C)

omit [Algebra B C] [IsScalarTower A B C] in
/-- `CommAlgCat.prodSndBaseMap` becomes invertible in `D(C)`. -/
theorem isIso_Q_map_prodSndBaseMap :
    IsIso (DerivedCategory.Q.map (prodSndBaseMap A B C)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ (prodSndBaseMap A B C)).2
    (quasiIso_prodSndBaseMap A B C)

/-- `CommAlgCat.prodSndTopMap` becomes invertible in `D(C)`. -/
theorem isIso_Q_map_prodSndTopMap :
    IsIso (DerivedCategory.Q.map (prodSndTopMap B C)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ (prodSndTopMap B C)).2
    (quasiIso_prodSndTopMap B C)

/-- **The second vertex descends.** Base change along `B × C → C` carries `L_{B×C/A}` to
`L_{C/A}`. -/
def descentIso₂ :
    (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategory.obj
        (fundamentalVertex₂.{u, u, u + 1} A (B × C)) ≅
      fundamentalVertex₂.{u, u, u + 1} A C :=
  haveI := isIso_Q_map_prodSndBaseMap A B C
  (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategoryFactors.app
      (cotangentComplex.{u, u} A (CommAlgCat.of A (B × C))) ≪≫
    asIso (DerivedCategory.Q.map (prodSndBaseMap A B C))

/-- **The third vertex descends.** Base change along `B × C → C` carries `L_{B×C/B}` to
`L_{C/B}`. -/
def descentIso₃ :
    (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategory.obj
        (fundamentalVertex₃.{u, u, u + 1} B (B × C)) ≅
      fundamentalVertex₃.{u, u, u + 1} B C :=
  haveI := isIso_Q_map_prodSndTopMap B C
  (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategoryFactors.app
      (cotangentComplex.{u, u} B (CommAlgCat.of B (B × C))) ≪≫
    asIso (DerivedCategory.Q.map (prodSndTopMap B C))

/-- **The first vertex descends.** Base change along `B × C → C` carries
`L_{B/A} ⊗^𝐋_B (B × C)` to `L_{B/A} ⊗^𝐋_B C`: the terms of `L_{B/A}` are projective, so both
derived base changes are computed degreewise, and the two degreewise base changes cancel by
`ModuleCat.extendScalarsCompComplexIso`. -/
def descentIso₁ :
    (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategory.obj
        (fundamentalVertex₁.{u, u, u + 1, u + 1} A B (B × C)) ≅
      fundamentalVertex₁.{u, u, u + 1, u + 1} A B C :=
  (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategory.mapIso
      (cotangentComplexDerivedBaseChangeTermwiseIso A (CommAlgCat.of A B) (B × C)) ≪≫
    (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategoryFactors.app
      (((ModuleCat.extendScalars (algebraMap B (B × C))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A (CommAlgCat.of A B))) ≪≫
    DerivedCategory.Q.mapIso
      ((ModuleCat.extendScalarsCompComplexIso (algebraMap B (B × C)) (RingHom.snd B C)
        (ComplexShape.up ℤ)).app (cotangentComplex.{u, u} A (CommAlgCat.of A B))) ≪≫
    (cotangentComplexDerivedBaseChangeTermwiseIso A (CommAlgCat.of A B) C).symm


/-! ### The two displayed morphisms descend -/

/-- **The first morphism descends.** At chain level: the functoriality map of
[Stacks, Tag 08PN] for `B → B × C` in the adjoint shape, base changed along `B × C → C` and
followed by `CommAlgCat.prodSndBaseMap`, is the functoriality map for `B → C`, read through the
cancellation of the two base changes. This is
`CommAlgCat.squareCotangentComplexMap_counit_comp_iterated` at the two squares
`CommAlgCat.displaySquare₁` and `CommAlgCat.productSndSquare`, whose horizontal composite is the
square `CommAlgCat.displaySquare₁` of `A → B → C`. -/
theorem prodSndBaseMap_cotangentExtendScalars :
    ((ModuleCat.extendScalars (RingHom.snd B C)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (cotangentExtendScalarsComplexMap (A := A) (A' := A) (B := CommAlgCat.of A B)
            (B' := CommAlgCat.of A (B × C)) (IsScalarTower.toAlgHom A B (B × C))) ≫
        prodSndBaseMap A B C =
      (ModuleCat.extendScalarsCompComplexIso (algebraMap B (B × C)) (RingHom.snd B C)
            (ComplexShape.up ℤ)).hom.app (cotangentComplex.{u, u} A (CommAlgCat.of A B)) ≫
        cotangentExtendScalarsComplexMap (A := A) (A' := A) (B := CommAlgCat.of A B)
          (B' := CommAlgCat.of A C) (IsScalarTower.toAlgHom A B C) := by
  rw [cotangentExtendScalarsComplexMap_eq_counit, cotangentExtendScalarsComplexMap_eq_counit]
  exact (squareCotangentComplexMap_counit_comp_iterated'.{u} (displaySquare₁ A B (B × C))
    (productSndSquare.{u, u} A (CommAlgCat.of A B) (CommAlgCat.of A C)))

/-- **The second morphism descends.** At chain level: the functoriality map of
[Stacks, Tag 08PN] for the change of base ring `A → B` at `B × C`, base changed along
`B × C → C` and followed by `CommAlgCat.prodSndTopMap`, is `CommAlgCat.prodSndBaseMap` followed
by the functoriality map for the change of base ring at `C`. Both composites are the adjoint map
of the square `(A → B, B × C → C)`, which is the two horizontal composites of the commuting
square of squares. -/
theorem prodSndTopMap_cotangentComplexBaseRingMap :
    ((ModuleCat.extendScalars (RingHom.snd B C)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (cotangentComplexBaseRingMap A B (B × C)) ≫ prodSndTopMap B C =
      prodSndBaseMap A B C ≫ cotangentComplexBaseRingMap A B C := by
  have hc := squareCotangentComplexMap_comp_counit.{u}
    (productSndSquare.{u, u} A (CommAlgCat.of A B) (CommAlgCat.of A C)) (displaySquare₂ A B C)
  have hcomp := squareCotangentComplexMap_comp'.{u} (displaySquare₂ A B (B × C))
    (productSndSquare.{u, u} B (CommAlgCat.of B B) (CommAlgCat.of B C))
  refine Eq.trans ?_ hc
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ ModuleCat.extendRestrictScalarsAdjCounitComplex
      (RingHom.snd B C) (ComplexShape.up ℤ) (cotangentComplex.{u, u} B (CommAlgCat.of B C)))
    (((ModuleCat.extendScalars (RingHom.snd B C)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map_comp _ _).symm) ?_
  exact congrArg (fun z =>
      ((ModuleCat.extendScalars (RingHom.snd B C)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map z ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex (RingHom.snd B C) (ComplexShape.up ℤ)
          (cotangentComplex.{u, u} B (CommAlgCat.of B C)))
    hcomp.symm

/-- **The first morphism of the descended triangle is the display's own first morphism.** -/
theorem productDisplayMor₁_eq_fundamentalMor₁ :
    (descentIso₁ A B C).inv ≫
          (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategory.map
            (fundamentalMor₁.{u} A B (B × C)) ≫ (descentIso₂ A B C).hom =
      fundamentalMor₁.{u} A B C := by
  have hkey := (ModuleCat.extendScalars.{u, u, u}
      (RingHom.snd B C)).mapDerivedCategoryFactors_hom_app_comp
    (cotangentExtendScalarsComplexMap (A := A) (A' := A) (B := CommAlgCat.of A B)
      (B' := CommAlgCat.of A (B × C)) (IsScalarTower.toAlgHom A B (B × C)))
    (prodSndBaseMap A B C)
  rw [Iso.inv_comp_eq, descentIso₁, descentIso₂, fundamentalMor₁, fundamentalMor₁]
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc]
  refine congrArg (fun z =>
    (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategory.map
      (cotangentComplexDerivedBaseChangeTermwiseIso A (CommAlgCat.of A B) (B × C)).hom ≫ z) ?_
  refine Eq.trans hkey ?_
  refine congrArg (fun z =>
    (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategoryFactors.hom.app
      (((ModuleCat.extendScalars (algebraMap B (B × C))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A (CommAlgCat.of A B))) ≫ z) ?_
  refine Eq.trans (congrArg DerivedCategory.Q.map
    (prodSndBaseMap_cotangentExtendScalars A B C)) ?_
  refine Eq.trans (DerivedCategory.Q.map_comp _ _) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (fun z => DerivedCategory.Q.map
      ((ModuleCat.extendScalarsCompComplexIso (algebraMap B (B × C)) (RingHom.snd B C)
        (ComplexShape.up ℤ)).hom.app (cotangentComplex.{u, u} A (CommAlgCat.of A B))) ≫ z)
    (Iso.inv_hom_id_assoc (cotangentComplexDerivedBaseChangeTermwiseIso A (CommAlgCat.of A B) C)
      _).symm

/-- **The second morphism of the descended triangle is the display's own second morphism.** -/
theorem productDisplayMor₂_eq_fundamentalMor₂ :
    (descentIso₂ A B C).inv ≫
          (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategory.map
            (fundamentalMor₂.{u} A B (B × C)) ≫ (descentIso₃ B C).hom =
      fundamentalMor₂.{u} A B C := by
  have hkey := (ModuleCat.extendScalars.{u, u, u}
      (RingHom.snd B C)).mapDerivedCategoryFactors_hom_app_comp
    (cotangentComplexBaseRingMap A B (B × C)) (prodSndTopMap B C)
  rw [Iso.inv_comp_eq, descentIso₂, descentIso₃, fundamentalMor₂, fundamentalMor₂]
  simp only [Iso.trans_hom, asIso_hom, Iso.app_hom, Category.assoc]
  rw [hkey, ← Functor.map_comp, prodSndTopMap_cotangentComplexBaseRingMap]

/-! ### The triangle -/

/-- **The third displayed morphism of [Stacks, Tag 08QS], for arbitrary ring maps
`A → B → C`.** It is the connecting morphism of the fundamental triangle of
`A → B → B × C`, base changed along the flat ring map `B × C → C` and read between the display's
own vertices `L_{C/B}` and `(L_{B/A} ⊗^𝐋_B C)⟦1⟧`. -/
@[stacks 08QS "the third displayed morphism `L_{C/B} → (L_{B/A} ⊗^𝐋_B C)[1]`, for arbitrary \
  ring maps `A → B → C`: the connecting morphism of the fundamental triangle of `A → B → B × C` \
  base changed along `B × C → C`, read between the display's own two vertices. The display is a \
  distinguished triangle on these three morphisms by \
  `CommAlgCat.productFundamentalTriangle_distinguished`"]
def productFundamentalMor₃ :
    fundamentalVertex₃.{u, u, u + 1} B C ⟶
      (fundamentalVertex₁.{u, u, u + 1, u + 1} A B C)⟦(1 : ℤ)⟧ :=
  (descentIso₃ B C).inv ≫
    ((ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategory.mapTriangle.obj
        (Triangle.mk (fundamentalMor₁.{u} A B (B × C)) (fundamentalMor₂.{u} A B (B × C))
          (fundamentalMor₃ A B (B × C) (injective_algebraMap_prod B C)))).mor₃ ≫
      ((descentIso₁ A B C).hom)⟦(1 : ℤ)⟧'

/-- **Stacks Project, Tag 08QX, and the distinguishedness asserted by the display of Tag 08QS.**
Let `A → B → C` be ring maps. Then

`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`

is a distinguished triangle in `D(C)`, on the three vertices of the display of
[Stacks, Tag 08QS], with the display's own first two morphisms
`CommAlgCat.fundamentalMor₁` and `CommAlgCat.fundamentalMor₂` — the two functoriality maps of
[Stacks, Tag 08PN] for the two commutative squares of the tower — and with
`CommAlgCat.productFundamentalMor₃` for its third.

The display of Tag 08QS is written as a triangle, and what makes it one is exactly this
statement, so the display's distinguishedness clause is registered here as well: the three
objects and the three arrows of the display are named by
`CommAlgCat.fundamentalVertex₁`, `CommAlgCat.fundamentalVertex₂`,
`CommAlgCat.fundamentalVertex₃`, `CommAlgCat.fundamentalMor₁`, `CommAlgCat.fundamentalMor₂` and
`CommAlgCat.productFundamentalMor₃`, and that they form a triangle at all is Proposition 08QX.

The proof is the one of [Stacks, Remark 08SD]: the triangle for `A → B → B × C`, where the map
is the split injection `b ↦ (b, f b)`, base changed along the flat projection `B × C → C`. -/
@[stacks 08QX "the proposition: for ring maps `A → B → C` the display of Tag 08QS is a \
  distinguished triangle in `D(C)`, on the display's own three vertices and with the display's \
  own three morphisms. The third of them is `CommAlgCat.productFundamentalMor₃`",
  stacks 08QS "the distinguishedness asserted by the display: Equation 92.7.0.1 is written as a \
  triangle, and that the display's three objects and three arrows form a DISTINGUISHED triangle \
  in `D(C)` is the remaining clause of the display, for arbitrary ring maps `A → B → C` with no \
  hypothesis on them. The display's three vertices are `CommAlgCat.fundamentalVertex₁`, \
  `CommAlgCat.fundamentalVertex₂` and `CommAlgCat.fundamentalVertex₃` and its three morphisms \
  are `CommAlgCat.fundamentalMor₁`, `CommAlgCat.fundamentalMor₂` and \
  `CommAlgCat.productFundamentalMor₃`, each of which carries the tag for its own constituent. \
  That the triangle is distinguished is Proposition 08QX, which this declaration also carries"]
theorem productFundamentalTriangle_distinguished :
    Triangle.mk (fundamentalMor₁.{u} A B C) (fundamentalMor₂.{u} A B C)
        (productFundamentalMor₃ A B C) ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) :=
  distTriang_of_iso_eq _
    ((ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategory.map_distinguished _
      (fundamentalTriangle_distinguished A B (B × C) (injective_algebraMap_prod B C)))
    (descentIso₁ A B C) (descentIso₂ A B C) (descentIso₃ B C)
    (productDisplayMor₁_eq_fundamentalMor₁ A B C) (productDisplayMor₂_eq_fundamentalMor₂ A B C)

/-- **[Stacks, Tag 08QX] in existential form, for arbitrary ring maps `A → B → C`.** -/
theorem exists_distTriang_fundamentalVertex :
    ∃ (α : fundamentalVertex₁.{u, u, u + 1, u + 1} A B C ⟶ fundamentalVertex₂.{u, u, u + 1} A C)
      (β : fundamentalVertex₂.{u, u, u + 1} A C ⟶ fundamentalVertex₃.{u, u, u + 1} B C)
      (δ : fundamentalVertex₃.{u, u, u + 1} B C ⟶
        (fundamentalVertex₁.{u, u, u + 1, u + 1} A B C)⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) :=
  ⟨_, _, _, productFundamentalTriangle_distinguished A B C⟩

/-! ### Lemma 08R3 -/

/-- **Stacks Project, Tag 08R3.** Let `A → B → C` be ring maps such that `L_{C/B} = 0`. Then
`L_{C/A} = L_{B/A} ⊗^𝐋_B C`: precisely, the first morphism `CommAlgCat.fundamentalMor₁` of the
fundamental triangle, `L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A}` in `D(C)`, is an isomorphism.

Here `L_{C/B} = 0` is `IsZero (CommAlgCat.fundamentalVertex₃ B C)`, the vanishing in `D(C)` of the
cotangent complex of `B → C`. The three rings `A`, `B`, `C` are taken in one universe `Type u`,
as for the triangle of [Stacks, Tag 08QX].

The proof is the source's: the fundamental triangle
`CommAlgCat.productFundamentalTriangle_distinguished` (Proposition 08QX) is distinguished, and a
distinguished triangle with vanishing third vertex has invertible first morphism
(`CommAlgCat.isIso_of_isZero_fundamentalVertex₃`). -/
@[stacks 08R3 "the lemma for arbitrary ring maps `A → B → C` with `A`, `B`, `C` in one universe: \
  if `L_{C/B} = 0` in `D(C)` (`IsZero (CommAlgCat.fundamentalVertex₃ B C)`, the cotangent complex \
  of `B → C`), then the first morphism \
  `CommAlgCat.fundamentalMor₁ : L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A}` of the fundamental triangle is an \
  isomorphism, i.e. `L_{C/A} = L_{B/A} ⊗^𝐋_B C`. Proved from the distinguished triangle of \
  Proposition 08QX, `CommAlgCat.productFundamentalTriangle_distinguished`"]
theorem isIso_fundamentalMor₁_of_isZero_fundamentalVertex₃
    (h : IsZero (fundamentalVertex₃.{u, u, u + 1} B C)) :
    IsIso (fundamentalMor₁.{u} A B C) :=
  isIso_of_isZero_fundamentalVertex₃.{u, u, u + 1, u + 1} A B C
    (productFundamentalTriangle_distinguished A B C) h

/-- **Stacks Project, Tag 08R3**, as an isomorphism. Let `A → B → C` be ring maps such that
`L_{C/B} = 0`. Then `L_{C/A} = L_{B/A} ⊗^𝐋_B C`, read as an isomorphism
`L_{B/A} ⊗^𝐋_B C ≅ L_{C/A}` in `D(C)` between the first and second vertices of the fundamental
triangle. The rings `A`, `B`, `C` are taken in one universe `Type u`. The isomorphism is the first
morphism of the distinguished triangle of [Stacks, Tag 08QX],
`CommAlgCat.productFundamentalTriangle_distinguished`; see
`CommAlgCat.isIso_fundamentalMor₁_of_isZero_fundamentalVertex₃`. -/
@[stacks 08R3 "the lemma for arbitrary ring maps `A → B → C` with `A`, `B`, `C` in one universe: \
  if `L_{C/B} = 0` in `D(C)`, then `L_{C/A} = L_{B/A} ⊗^𝐋_B C`, read as an isomorphism \
  `CommAlgCat.fundamentalVertex₁ A B C ≅ CommAlgCat.fundamentalVertex₂ A C` in `D(C)`. Proved \
  from the distinguished triangle of Proposition 08QX, \
  `CommAlgCat.productFundamentalTriangle_distinguished`"]
theorem nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero_fundamentalVertex₃
    (h : IsZero (fundamentalVertex₃.{u, u, u + 1} B C)) :
    Nonempty (fundamentalVertex₁.{u, u, u + 1, u + 1} A B C ≅
      fundamentalVertex₂.{u, u, u + 1} A C) :=
  nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero.{u, u, u + 1, u + 1} A B C
    (productFundamentalTriangle_distinguished A B C) h

end Tower

end CommAlgCat

end
