module

public import StacksFrontier.Cotangent.BaseChangeComplexCounit
public import StacksFrontier.Cotangent.ProductDecomposition
public import StacksFrontier.Homology.ExtendScalars.ProductRing

/-!
# Tag 08SC reduced to its two components

The canonical map of [Stacks, Tag 08SC],

`L_{B×C/A} ⟶ L_{B/A} ⊕ L_{C/A}`,

is a map of complexes of `B × C`-modules, and
`ModuleCat.quasiIso_of_quasiIso_extendScalars_prod` of
`StacksFrontier/Homology/ExtendScalars/ProductRing.lean` says that such a map is a
quasi-isomorphism as soon as its two base changes along the projections are. This file carries
out that reduction, and the simplification which makes it worth doing: **each of the two base
changes sees only one summand.** Base change along `B × C → B` kills `L_{C/A}` read over
`B × C`, by `ModuleCat.isZero_extendScalars_fst_restrictScalars_snd`, so it turns the projection
`L_{B/A} ⊕ L_{C/A} ⟶ L_{B/A}` into an isomorphism, and the base change of the canonical map
becomes the base change of its first component alone.

So Tag 08SC holds as soon as the two *component* statements do:

`L_{B×C/A} ⊗_{B×C} B = L_{B/A}` and `L_{B×C/A} ⊗_{B×C} C = L_{C/A}`,

each of which asks that one functoriality map of [Stacks, Tag 08PN] become invertible after one
base change — exactly the shape that [Stacks, Tag 08QQ] inverts.

## Main results

* `CategoryTheory.Functor.isIso_map_biprod_fst` and
  `CategoryTheory.Functor.isIso_map_biprod_snd`: an additive functor killing one summand of a
  binary biproduct inverts the projection onto the other.
* `CommAlgCat.isIso_extendScalars_biprod_fst` and `CommAlgCat.isIso_extendScalars_biprod_snd`:
  the two base changes along the projections of `B × C` invert the two projections of
  `L_{B/A} ⊕ L_{C/A}`.
* `CommAlgCat.quasiIso_cotangentComplexProductMap_of_components`: **[Stacks, Tag 08SC] follows
  from its two components**, each stated as the functoriality map of [Stacks, Tag 08PN] becoming
  a quasi-isomorphism after one base change.
* `CommAlgCat.quasiIso_cotangentComplexProductMap_of_components_counit`: the same, with the two
  components in the adjoint shape `L_{B×C/A} ⊗_{B×C} B ⟶ L_{B/A}` that [Stacks, Tag 08QQ]
  inverts — the counit being invertible because the projections are surjective.

## Implementation notes

That an additive functor killing `Y` inverts `biprod.fst : X ⊞ Y ⟶ X` is read off from
`CategoryTheory.biprod.total`: applying the functor to
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙` and dropping the second summand leaves
`F(biprod.fst) ≫ F(biprod.inl) = 𝟙`, while `F(biprod.inl) ≫ F(biprod.fst) = 𝟙` is functoriality.
The hypothesis is taken in the form `F.map biprod.snd = 0` rather than `IsZero (F.obj Y)`: for
complexes the vanishing is degreewise, and a degreewise vanishing morphism is the zero morphism
without any statement about the complex being a zero object.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite

universe u v

namespace CategoryTheory.Functor

variable {D E : Type*} [Category D] [Category E] [Preadditive D] [Preadditive E]
  (F : D ⥤ E) [F.Additive] {X Y : D} [HasBinaryBiproduct X Y]

/-- **An additive functor killing the second summand inverts the first projection of a binary
biproduct.** Applying `F` to `biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙` and
dropping the second summand leaves `F(biprod.fst) ≫ F(biprod.inl) = 𝟙`; the other composite is
`F` of `biprod.inl ≫ biprod.fst = 𝟙`. -/
theorem isIso_map_biprod_fst (hY : F.map (biprod.snd : X ⊞ Y ⟶ Y) = 0) :
    IsIso (F.map (biprod.fst : X ⊞ Y ⟶ X)) := by
  refine ⟨F.map (biprod.inl : X ⟶ X ⊞ Y), ?_, ?_⟩
  · have h := congrArg F.map (biprod.total (X := X) (Y := Y))
    rw [F.map_add, F.map_comp, F.map_comp, F.map_id, hY, zero_comp, add_zero] at h
    exact h
  · rw [← F.map_comp, biprod.inl_fst, F.map_id]

/-- **An additive functor killing the first summand inverts the second projection of a binary
biproduct.** -/
theorem isIso_map_biprod_snd (hX : F.map (biprod.fst : X ⊞ Y ⟶ X) = 0) :
    IsIso (F.map (biprod.snd : X ⊞ Y ⟶ Y)) := by
  refine ⟨F.map (biprod.inr : Y ⟶ X ⊞ Y), ?_, ?_⟩
  · have h := congrArg F.map (biprod.total (X := X) (Y := Y))
    rw [F.map_add, F.map_comp, F.map_comp, F.map_id, hX, zero_comp, zero_add] at h
    exact h
  · rw [← F.map_comp, biprod.inr_snd, F.map_id]

end CategoryTheory.Functor

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B C : CommAlgCat.{max u v} A)

/-- **Base change along `B × C → B` inverts the first projection of `L_{B/A} ⊕ L_{C/A}`.** The
second summand, `L_{C/A}` read over `B × C` along the second projection, is killed degreewise by
`ModuleCat.isZero_extendScalars_fst_restrictScalars_snd`. -/
theorem isIso_extendScalars_biprod_fst :
    IsIso (((ModuleCat.extendScalars (productFstSquare.{u, v} A B C).map).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (biprod.fst (X :=
        ((ModuleCat.restrictScalars (productFstSquare.{u, v} A B C).map).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, v} A B)) (Y :=
        ((ModuleCat.restrictScalars (productSndSquare.{u, v} A B C).map).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, v} A C)))) :=
  Functor.isIso_map_biprod_fst _
    (HomologicalComplex.hom_ext _ _ fun n =>
      (ModuleCat.isZero_extendScalars_fst_restrictScalars_snd
        ((cotangentComplex.{u, v} A C).X n)).eq_of_tgt _ _)

/-- **Base change along `B × C → C` inverts the second projection of `L_{B/A} ⊕ L_{C/A}`.** -/
theorem isIso_extendScalars_biprod_snd :
    IsIso (((ModuleCat.extendScalars (productSndSquare.{u, v} A B C).map).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (biprod.snd (X :=
        ((ModuleCat.restrictScalars (productFstSquare.{u, v} A B C).map).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, v} A B)) (Y :=
        ((ModuleCat.restrictScalars (productSndSquare.{u, v} A B C).map).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, v} A C)))) :=
  Functor.isIso_map_biprod_snd _
    (HomologicalComplex.hom_ext _ _ fun n =>
      (ModuleCat.isZero_extendScalars_snd_restrictScalars_fst
        ((cotangentComplex.{u, v} A B).X n)).eq_of_tgt _ _)

/-- A map whose image under `F` becomes a quasi-isomorphism after composing with an `F`-image
isomorphism is itself sent to a quasi-isomorphism. -/
private theorem quasiIso_map_of_isIso_map_comp {ι : Type*} {c : ComplexShape ι} {R S : Type u}
    [CommRing R] [CommRing S] {F : HomologicalComplex (ModuleCat.{max u v} R) c ⥤
      HomologicalComplex (ModuleCat.{max u v} S) c} {X Y Z : HomologicalComplex (ModuleCat R) c}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hg : IsIso (F.map g)) (h : QuasiIso (F.map (f ≫ g))) :
    QuasiIso (F.map f) := by
  rw [F.map_comp] at h
  exact quasiIso_of_comp_right _ (F.map g)

/-- A map to the base change of a restriction is a quasi-isomorphism once its composite with the
counit is, when the ring map is surjective. -/
private theorem quasiIso_of_quasiIso_comp_counit {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{u} S) c} {L : HomologicalComplex (ModuleCat.{u} S) c}
    (g : L ⟶ ((ModuleCat.extendScalars f).mapHomologicalComplex c).obj
      (((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj K))
    (h : QuasiIso (g ≫ ModuleCat.extendRestrictScalarsAdjCounitComplex f c K)) : QuasiIso g := by
  have := ModuleCat.isIso_extendRestrictScalarsAdjCounitComplex f c hf K
  exact quasiIso_of_comp_right _ (ModuleCat.extendRestrictScalarsAdjCounitComplex f c K)

/-- **[Stacks, Tag 08SC] follows from its two components.** If the functoriality map of
[Stacks, Tag 08PN] for the first projection becomes a quasi-isomorphism after base change along
that projection, and likewise for the second, then the canonical map
`L_{B×C/A} ⟶ L_{B/A} ⊕ L_{C/A}` is a quasi-isomorphism.

The two base changes of the canonical map are, up to the isomorphisms
`CommAlgCat.isIso_extendScalars_biprod_fst` and `CommAlgCat.isIso_extendScalars_biprod_snd`, the
base changes of its two components; and a map of complexes of `B × C`-modules whose two base
changes are quasi-isomorphisms is one, by
`ModuleCat.quasiIso_of_quasiIso_extendScalars_prod`. -/
theorem quasiIso_cotangentComplexProductMap_of_components
    (hB : QuasiIso (((ModuleCat.extendScalars
          (productFstSquare.{u, v} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (squareCotangentComplexMap.{u, v, u} (productFstSquare.{u, v} A B C))))
    (hC : QuasiIso (((ModuleCat.extendScalars
          (productSndSquare.{u, v} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (squareCotangentComplexMap.{u, v, u} (productSndSquare.{u, v} A B C)))) :
    QuasiIso (cotangentComplexProductMap.{u, v} A B C) := by
  refine ModuleCat.quasiIso_of_quasiIso_extendScalars_prod
    (cotangentComplexProductMap.{u, v} A B C) ?_ ?_
  · exact quasiIso_map_of_isIso_map_comp _ biprod.fst
      (isIso_extendScalars_biprod_fst.{u, v} A B C)
      (by rw [cotangentComplexProductMap_fst.{u, v} A B C]; exact hB)
  · exact quasiIso_map_of_isIso_map_comp _ biprod.snd
      (isIso_extendScalars_biprod_snd.{u, v} A B C)
      (by rw [cotangentComplexProductMap_snd.{u, v} A B C]; exact hC)

/-- **[Stacks, Tag 08SC] follows from its two components, in the adjoint shape.** The two
component maps are here written as [Stacks, Tag 08QQ] writes them -- extension of scalars of the
functoriality map of [Stacks, Tag 08PN] followed by the counit, which is
`CommAlgCat.cotangentExtendScalarsComplexMap_eq_counit` -- so this is the form in which Tag 08QQ
discharges them. The counit is invertible because the two projections of `B × C` are surjective
(`ModuleCat.isIso_extendRestrictScalarsAdjCounitComplex`). -/
theorem quasiIso_cotangentComplexProductMap_of_components_counit
    (hB : QuasiIso (((ModuleCat.extendScalars
            (productFstSquare.{u, v} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, v, u} (productFstSquare.{u, v} A B C)) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex (productFstSquare.{u, v} A B C).map
          (ComplexShape.up ℤ) (cotangentComplex.{u, v} A B)))
    (hC : QuasiIso (((ModuleCat.extendScalars
            (productSndSquare.{u, v} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, v, u} (productSndSquare.{u, v} A B C)) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex (productSndSquare.{u, v} A B C).map
          (ComplexShape.up ℤ) (cotangentComplex.{u, v} A C))) :
    QuasiIso (cotangentComplexProductMap.{u, v} A B C) := by
  refine quasiIso_cotangentComplexProductMap_of_components.{u, v} A B C ?_ ?_
  · exact quasiIso_of_quasiIso_comp_counit _ (RingHom.surjective_fst _ _) _ hB
  · exact quasiIso_of_quasiIso_comp_counit _ (RingHom.surjective_snd _ _) _ hC

end CommAlgCat

end
