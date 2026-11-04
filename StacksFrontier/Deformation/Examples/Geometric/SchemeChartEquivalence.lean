module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.CofiberedPresentation.Criteria
public import StacksFrontier.Deformation.Examples.Geometric.SchemeRingDeformation
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCover
public import StacksFrontier.Deformation.RimSchlessinger.FibreProduct.Deformations
public import StacksFrontier.Deformation.Smooth.FullVertical

/-!
# The deformation category of an affine open and of its coordinate ring

[Stacks Project, Tag 0DYX] identifies the deformation category of an affine scheme with that of
its coordinate ring, over `𝒞_Λ`; it is
`Deformation.Examples.SchemeRingDeformation.equivalenceOver`, and it is stated for the scheme
`Spec P` on the nose. In Situation 0DYY the affine opens of `X` are *presented* as spectra, by
isomorphisms `U ≅ Spec P` over `Spec k`, so the identification has to be composed with the
transport of deformations along such an isomorphism. That composite is
`Deformation.Examples.chartEquivalenceOver`.

Two consequences follow: the deformation category of an affine open is cofibered in groupoids,
and the comparison functor to the deformation category of the coordinate ring is smooth.

## Main definitions

* `Deformation.Examples.transportEquivalenceOver`: transport of deformations along an
  isomorphism of the scheme being deformed, as an equivalence over `𝒞_Λ`.
* `Deformation.Examples.chartEquivalenceOver`: **Stacks 0DYX** for an affine open presented as a
  spectrum — the equivalence `Def_U ≃ Def_P` over `𝒞_Λ`.
* `Deformation.Examples.chartBasedFunctor`: the comparison `Def_U ⟶ Def_P` over `𝒞_Λ`.

## Main results

* `Deformation.Examples.isCofiberedInGroupoids_chart`: the deformation category of an affine
  open presented as a spectrum is cofibered in groupoids.
* `Deformation.Examples.isSmooth_chartBasedFunctor`: the comparison is smooth.

## Implementation notes

Transport along an isomorphism `i` changes only the identification of the special fibre, from
`ι` to `i ≫ ι`, so the two round trips are isomorphic to the identity by isomorphisms *whose
base and total-space components are identities*; that is why the unit and the counit are
visibly `2`-cells over `𝒞_Λ`, which is what
`StacksRepresentableCFG.EquivalenceOver` asks for.

## References

* [Stacks Project, Tag 0DYX](https://stacks.math.columbia.edu/tag/0DYX)
* [Stacks Project, Tag 0DYY](https://stacks.math.columbia.edu/tag/0DYY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Transport along an isomorphism of the scheme being deformed -/

section Transport

variable {X Y : Over (Spec (.of k))} (e : Y ≅ X)

/-- The underlying morphism of schemes of an isomorphism over `Spec k` is an isomorphism. -/
instance isIso_iso_hom_left : IsIso e.hom.left := by
  change IsIso ((Over.forget (Spec (CommRingCat.of k))).map e.hom)
  infer_instance

/-- The underlying morphism of schemes of the inverse of an isomorphism over `Spec k` is an
isomorphism. -/
instance isIso_iso_inv_left : IsIso e.inv.left := by
  change IsIso ((Over.forget (Spec (CommRingCat.of k))).map e.inv)
  infer_instance

/-- Transport of deformations from `X` to `Y` along an isomorphism `Y ≅ X` over `Spec k`. -/
abbrev transportFst : SchemeDeformationCategory (Λ := Λ) (k := k) X ⥤
    SchemeDeformationCategory (Λ := Λ) (k := k) Y :=
  transportDeformationFunctor e.hom.left (Over.w e.hom)

/-- Transport of deformations back from `Y` to `X`. -/
abbrev transportSnd : SchemeDeformationCategory (Λ := Λ) (k := k) Y ⥤
    SchemeDeformationCategory (Λ := Λ) (k := k) X :=
  transportDeformationFunctor e.inv.left (Over.w e.inv)

/-- Transporting a deformation of `X` to `Y` and back gives it again. -/
def transportUnitApp (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    P ≅ (transportFst (Λ := Λ) e ⋙ transportSnd (Λ := Λ) e).obj P where
  hom :=
    { base := 𝟙 P.base
      map := 𝟙 P.scheme
      cartesian := by
        have h : IsPullback (𝟙 P.scheme) P.toBase P.toBase (baseSpecMap (𝟙 P.base)) := by
          rw [baseSpecMap_id]
          exact IsPullback.id_horiz P.toBase
        exact h
      special_compat := by
        change (e.inv.left ≫ e.hom.left ≫ P.specialMap) ≫ 𝟙 P.scheme = P.specialMap
        rw [Category.comp_id, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left,
          Category.id_comp] }
  inv :=
    { base := 𝟙 P.base
      map := 𝟙 P.scheme
      cartesian := by
        have h : IsPullback (𝟙 P.scheme) P.toBase P.toBase (baseSpecMap (𝟙 P.base)) := by
          rw [baseSpecMap_id]
          exact IsPullback.id_horiz P.toBase
        exact h
      special_compat := by
        change P.specialMap ≫ 𝟙 P.scheme = e.inv.left ≫ e.hom.left ≫ P.specialMap
        rw [Category.comp_id, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left,
          Category.id_comp] }
  hom_inv_id := SchemeDeformationCategory.Hom.ext (Category.comp_id _) (Category.comp_id _)
  inv_hom_id := SchemeDeformationCategory.Hom.ext (Category.comp_id _) (Category.comp_id _)

/-- Transporting a deformation of `Y` to `X` and back gives it again. -/
def transportCounitApp (P : SchemeDeformationCategory (Λ := Λ) (k := k) Y) :
    (transportSnd (Λ := Λ) e ⋙ transportFst (Λ := Λ) e).obj P ≅ P where
  hom :=
    { base := 𝟙 P.base
      map := 𝟙 P.scheme
      cartesian := by
        have h : IsPullback (𝟙 P.scheme) P.toBase P.toBase (baseSpecMap (𝟙 P.base)) := by
          rw [baseSpecMap_id]
          exact IsPullback.id_horiz P.toBase
        exact h
      special_compat := by
        change P.specialMap ≫ 𝟙 P.scheme = e.hom.left ≫ e.inv.left ≫ P.specialMap
        rw [Category.comp_id, ← Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left,
          Category.id_comp] }
  inv :=
    { base := 𝟙 P.base
      map := 𝟙 P.scheme
      cartesian := by
        have h : IsPullback (𝟙 P.scheme) P.toBase P.toBase (baseSpecMap (𝟙 P.base)) := by
          rw [baseSpecMap_id]
          exact IsPullback.id_horiz P.toBase
        exact h
      special_compat := by
        change (e.hom.left ≫ e.inv.left ≫ P.specialMap) ≫ 𝟙 P.scheme = P.specialMap
        rw [Category.comp_id, ← Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left,
          Category.id_comp] }
  hom_inv_id := SchemeDeformationCategory.Hom.ext (Category.comp_id _) (Category.comp_id _)
  inv_hom_id := SchemeDeformationCategory.Hom.ext (Category.comp_id _) (Category.comp_id _)

/-- The unit of the transport equivalence. -/
def transportUnitIso :
    𝟭 (SchemeDeformationCategory (Λ := Λ) (k := k) X) ≅
      transportFst (Λ := Λ) e ⋙ transportSnd (Λ := Λ) e :=
  NatIso.ofComponents (transportUnitApp (Λ := Λ) e) (fun {P Q} f => by
    have hb : f.base ≫ 𝟙 Q.base = 𝟙 P.base ≫ f.base := by
      rw [Category.comp_id, Category.id_comp]
    have hm : (𝟙 Q.scheme : Q.scheme ⟶ Q.scheme) ≫ f.map = f.map ≫ 𝟙 P.scheme := by
      rw [Category.comp_id, Category.id_comp]
    exact SchemeDeformationCategory.Hom.ext hb hm)

/-- The counit of the transport equivalence. -/
def transportCounitIso :
    transportSnd (Λ := Λ) e ⋙ transportFst (Λ := Λ) e ≅
      𝟭 (SchemeDeformationCategory (Λ := Λ) (k := k) Y) :=
  NatIso.ofComponents (transportCounitApp (Λ := Λ) e) (fun {P Q} f => by
    have hb : f.base ≫ 𝟙 Q.base = 𝟙 P.base ≫ f.base := by
      rw [Category.comp_id, Category.id_comp]
    have hm : (𝟙 Q.scheme : Q.scheme ⟶ Q.scheme) ≫ f.map = f.map ≫ 𝟙 P.scheme := by
      rw [Category.comp_id, Category.id_comp]
    exact SchemeDeformationCategory.Hom.ext hb hm)

/-- **Transport of deformations along an isomorphism of the scheme being deformed is an
equivalence over `𝒞_Λ`.** Both functors keep the object of `𝒞_Λ` on the nose, and the unit and
the counit have identity components on the bases and on the total spaces. -/
def transportEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Y) where
  hom := ⟨transportFst (Λ := Λ) e, transportDeformationFunctor_comp_projection _ _⟩
  inv := ⟨transportSnd (Λ := Λ) e, transportDeformationFunctor_comp_projection _ _⟩
  unitIso := transportUnitIso (Λ := Λ) e
  counitIso := transportCounitIso (Λ := Λ) e
  unit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun P => ?_)
    exact (inferInstance :
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift
        ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).map
          ((transportUnitIso (Λ := Λ) e).hom.app P))
        ((transportUnitIso (Λ := Λ) e).hom.app P))
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun P => ?_)
    exact (inferInstance :
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Y).IsHomLift
        ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) Y).map
          ((transportCounitIso (Λ := Λ) e).hom.app P))
        ((transportCounitIso (Λ := Λ) e).hom.app P))

end Transport

/-! ### The deformation category of an affine open and of its coordinate ring -/

section Chart

variable {X : Over (Spec (.of k))} {U : X.left.Opens} (P : Type u) [CommRing P] [Algebra k P]
  (e : Over.mk (U.ι ≫ X.hom) ≅ specOver k P)

/-- **Stacks 0DYX for an affine open presented as a spectrum.** The deformation category of an
open `U` of `X` which is presented as `Spec P` over `Spec k` is equivalent, over `𝒞_Λ`, to the
deformation category of the `k`-algebra `P`: transport the deformations along the presentation
and then take global sections. -/
@[stacks 0DYX "for an affine open presented as a spectrum by an isomorphism over Spec k, which \
is the form Situation 0DYY provides"]
def chartEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom)))
      (Over.forget (residueFieldAlgebra (Λ := Λ) (k := k) P) ⋙
        FlatAlgebraCategory.projection (Λ := Λ) (k := k)) :=
  (transportEquivalenceOver (Λ := Λ) e.symm).trans (SchemeRingDeformation.equivalenceOver P)

/-- The comparison morphism `Def_U ⟶ Def_P` over `𝒞_Λ`. -/
def chartBasedFunctor :
    BasedFunctor
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom))))
      (BasedCategory.ofFunctor
        (Over.forget (residueFieldAlgebra (Λ := Λ) (k := k) P) ⋙
          FlatAlgebraCategory.projection (Λ := Λ) (k := k))) where
  toFunctor := (chartEquivalenceOver (Λ := Λ) P e).hom.functor
  w := (chartEquivalenceOver (Λ := Λ) P e).hom.w

/-- The comparison morphism `Def_U ⟶ Def_P` is smooth, being an equivalence over `𝒞_Λ`. -/
theorem isSmooth_chartBasedFunctor :
    IsSmooth (chartBasedFunctor (Λ := Λ) P e) :=
  isSmooth_of_equivalenceOver (chartEquivalenceOver (Λ := Λ) P e) _ rfl

include e in
/-- **The deformation category of an affine open presented as a spectrum is cofibered in
groupoids.** This has no scheme-side proof in this repository: it is transported from the
deformation category of the coordinate ring, which is a deformation category by Tag 0DY2. -/
@[stacks 0DY7 "the deformation category of an affine open presented as a spectrum is cofibered \
in groupoids, transported along Tag 0DYX from the ring side; the clause for a general scheme is \
not covered"]
theorem isCofiberedInGroupoids_chart :
    IsCofiberedInGroupoids
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom))) :=
  isCofiberedInGroupoids_of_equivalenceOver (chartEquivalenceOver (Λ := Λ) P e).symm
    (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P).predeformation.cofibered

/-- The comparison morphism is full. -/
theorem full_chartBasedFunctor : (chartBasedFunctor (Λ := Λ) P e).toFunctor.Full := by
  have h : (chartEquivalenceOver (Λ := Λ) P e).hom.functor.IsEquivalence :=
    (chartEquivalenceOver (Λ := Λ) P e).isEquivalence_hom_functor
  exact (inferInstance : (chartEquivalenceOver (Λ := Λ) P e).hom.functor.Full)

/-- The comparison morphism is faithful. -/
theorem faithful_chartBasedFunctor : (chartBasedFunctor (Λ := Λ) P e).toFunctor.Faithful := by
  have h : (chartEquivalenceOver (Λ := Λ) P e).hom.functor.IsEquivalence :=
    (chartEquivalenceOver (Λ := Λ) P e).isEquivalence_hom_functor
  exact (inferInstance : (chartEquivalenceOver (Λ := Λ) P e).hom.functor.Faithful)

/-- Every deformation of `P` receives a vertical isomorphism from the image of a deformation
of `U`. -/
theorem exists_vertical_chartBasedFunctor
    (D : (BasedCategory.ofFunctor
      (Over.forget (residueFieldAlgebra (Λ := Λ) (k := k) P) ⋙
        FlatAlgebraCategory.projection (Λ := Λ) (k := k))).obj) :
    ∃ (Y : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom)))
      (a : (chartBasedFunctor (Λ := Λ) P e).obj Y ⟶ D),
      (Over.forget (residueFieldAlgebra (Λ := Λ) (k := k) P) ⋙
        FlatAlgebraCategory.projection (Λ := Λ) (k := k)).IsHomLift
        (𝟙 ((Over.forget (residueFieldAlgebra (Λ := Λ) (k := k) P) ⋙
          FlatAlgebraCategory.projection (Λ := Λ) (k := k)).obj D)) a :=
  ⟨(chartEquivalenceOver (Λ := Λ) P e).inv.functor.obj D,
    (chartEquivalenceOver (Λ := Λ) P e).counitIso.hom.app D,
    (chartEquivalenceOver (Λ := Λ) P e).isHomLift_counitIso_hom_app D⟩

end Chart

end Deformation.Examples

end
