module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit
import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility of `M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)` under dévissage in `L`

Let `(C, O)` be a ringed site and let `M` be an object of `D(O)`. For an object `L` of `D(O)`
Stacks 08JD supplies the canonical map

`Φ_L : M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)`,

`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom`. This file records the closure
properties of the class of objects `L` at which `Φ_L` is invertible that follow from the
contravariant functoriality of `Φ` in `L` and from the additivity of its source and target in
`L`: the class is closed under isomorphism, contains the zero objects, is closed under retracts
— that is, under passing to a direct summand in `D(O)` — and is closed under finite direct
sums, hence under direct summands of finite direct sums of its members. The two closure
properties in the variable `M` are recorded as well.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_iso`
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isZero`
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_retract`
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_iso_target`
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isZero_target`
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_sum_id`: invertibility at
  a direct summand of a finite direct sum of objects at which the map is invertible.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_biproduct`

## Implementation notes

The closure properties in `L` are consequences of one input,
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_naturality_source`: a morphism
`f : L' ⟶ L` makes the square with `Φ_L`, `Φ_{L'}`, the induced map `L^∨ ⟶ (L')^∨` tensored
with `M`, and `RSheafHom(f, M)` commute. A retract datum in `D(O)` therefore exhibits
`Φ_L` as a retract of `Φ_{L'}` in the category of arrows, and a retract of an isomorphism is
an isomorphism. The two properties in `M` come from the naturality in `M`,
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_naturality`.

For the zero objects the source and the target of `Φ_L` are both zero: `RSheafHom(-, N)` is
additive, by `AlgebraicGeometry.RingedSite.additive_derivedSheafHom_flip_obj`, so it carries a
zero object to a zero object, and `M ⊗^L_O -` is triangulated by the `exact_right` field of the
derived tensor product datum, hence additive.

The sum statement is phrased as a decomposition of the identity of `L`, as the single identity
`∑ k ∈ s, r k ≫ i k = 𝟙 L` through objects `L' k`, rather than in terms of a biproduct. That
form is what the argument uses and it covers both the retract case (a one-element sum) and the
biproduct case; the biproduct statement is deduced from it by `CategoryTheory.biproduct.total`.
Its proof reads the source and the target of `Φ` as the *additive* contravariant functors
`(-)^∨ ⋙ (M ⊗^L_O -)` and `RSheafHom(-, M)` of the dualized object, the first of these being
`tensorDualSourceFunctor` below; additivity of the tensor factor is `exact_right` again, through
Mathlib's instance that a triangulated functor is additive.

The universes are the diagonal `RingedSite.{u, u, u}` with the standard derived category, as in
every file of the derived internal Hom cluster.

## What this file does not contain

None of the four assertions of Stacks 08JJ is proved here, and in particular the third one is
not: no declaration below asserts that `Φ_L` is invertible for a perfect `L`. That assertion
itself — the isomorphism `M ⊗^L_O L^∨ ≅ RSheafHom(L, M)` — *is* in the library, as
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom`, by a route that
bypasses `Φ` entirely: the diagonal of Stacks 0BYS at target object the structure sheaf, which
Stacks 0ATN makes invertible at a perfect internal-Hom source. The identification of that
isomorphism with `Φ_L` **is** in the library, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHomCanonical`, and
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect` there is the
third assertion of Stacks 08JJ for `Φ_L` itself, so the dévissage below is not the only route
to `Φ_L`. What the statements
below give is the dévissage half of the source's argument for that assertion, with
no base case: the class of objects at which `Φ_L` is invertible is shown to be closed under the
operations the source's reduction performs, but the only object at which invertibility is
established outright is the zero object. The source finishes by restricting to a covering on
which `L` is a strictly perfect complex `E` and comparing `Φ` on representatives with the
module-level map `F ⊗_O Hom_O(E, O) ⟶ Hom_O(E, F)`, which is invertible by
`Stacks.SheafOfModules.isIso_tensorDualToSheafHom_of_localSummand`. Two inputs of that step were
absent from the library when this file was written. Both are now partly in place, and neither is
complete:

* the description of `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` on
  representatives is `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_kFlatModel`, in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualRepresentatives`:
  read through the comparisons, `Φ` is the class of the chain-level composition morphism of
  Stacks 0A91. What that leaves is the identification of *that* chain map, with its Koszul
  signs, with the module-level rank-one map, together with the tensor-side analogue of
  Stacks 08JH;
* the compatibility of `Φ` with restriction to a slice is available at the chain level, as
  `AlgebraicGeometry.RingedSite.compositionMap_restrict_square` in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionRestriction`. The derived
  statement is still absent, but its tensor-side input is no longer: the derived tensor product
  analogue of Stacks 08JB is
  `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso` in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceJunction`,
  natural in both variables, and the isomorphism alone is
  `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIso`, public since
  `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASlice`, and that
  isomorphism is transported across the canonical map to the ordinary total tensor product by
  `Stacks.DerivedTensor.SliceRestriction.toTensor_restrict_square` in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ToTensorRestriction`, which is the
  form the evaluation-source comparison of derived composition needs. What remains is the
  derived form of the chain-level square, without which the locality step
  `Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` cannot be applied to `Φ`; the
  two inputs it still owes are named in the section "What this file does not contain" of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionRestriction`.

## References

* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- **The canonical map of Stacks 08JD is invertible at an object as soon as it is invertible
at an isomorphic one.** The two canonical maps are intertwined by the maps induced on the duals
and on the internal Homs, and both of those are invertible. -/
theorem isIso_derivedTensorDualToSheafHom_of_iso
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : L ≅ L')
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : IsIso (derivedTensorDualToSheafHom X T L' M)) :
    IsIso (derivedTensorDualToSheafHom X T L M) := by
  have he : IsIso e.hom := e.isIso_hom
  have hdual : IsIso ((T.tensor.obj M).map
      (((derivedSheafHomBifunctor X).map e.hom.op).app (derivedStructureSheaf X))) := by
    have : IsIso (((derivedSheafHomBifunctor X).map e.hom.op).app (derivedStructureSheaf X)) :=
      inferInstance
    exact Functor.map_isIso _ _
  have hhom : IsIso (((derivedSheafHomBifunctor X).map e.hom.op).app M) := inferInstance
  have key := derivedTensorDualToSheafHom_naturality_source X T e.hom M
  have hrhs : IsIso ((T.tensor.obj M).map
        (((derivedSheafHomBifunctor X).map e.hom.op).app (derivedStructureSheaf X)) ≫
      derivedTensorDualToSheafHom X T L M) := by
    rw [key]
    have := h
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((T.tensor.obj M).map
      (((derivedSheafHomBifunctor X).map e.hom.op).app (derivedStructureSheaf X)))
    (derivedTensorDualToSheafHom X T L M)

/-- **The canonical map of Stacks 08JD is invertible at a zero object.** Both its source and
its target are zero: `RSheafHom(-, N)` and `M ⊗^L_O -` are additive, so they carry a zero
object to a zero object. -/
theorem isIso_derivedTensorDualToSheafHom_of_isZero
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hL : IsZero L)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (derivedTensorDualToSheafHom X T L M) := by
  have hop : IsZero (op L) := hL.op
  have htarget : IsZero (((derivedSheafHomBifunctor X).obj (op L)).obj M) :=
    Functor.map_isZero ((derivedSheafHomBifunctor X).flip.obj M) hop
  have hdual : IsZero (derivedDual X L) :=
    Functor.map_isZero ((derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X)) hop
  have hsource : IsZero ((T.tensor.obj M).obj (derivedDual X L)) :=
    Functor.map_isZero (T.tensor.obj M) hdual
  exact hsource.isIso htarget _

/-- Invertibility of `Φ_L` at a direct summand of a finite sum, by naturality in `L`. -/
private theorem isIso_derivedTensorDualToSheafHom_of_sum_id_aux
    {ι : Type*} (s : Finset ι)
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {L' : ι → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (i : ∀ k, L' k ⟶ L) (r : ∀ k, L ⟶ L' k)
    (hir : ∑ k ∈ s, r k ≫ i k = 𝟙 L)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ k, IsIso (derivedTensorDualToSheafHom X T (L' k) M)) :
    IsIso (derivedTensorDualToSheafHom X T L M) := by
  let F := (derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X) ⋙ T.tensor.obj M
  let G := (derivedSheafHomBifunctor X).flip.obj M
  have hnat : ∀ {A B : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (f : A ⟶ B),
      F.map f.op ≫ derivedTensorDualToSheafHom X T A M =
        derivedTensorDualToSheafHom X T B M ≫ G.map f.op :=
    fun f => derivedTensorDualToSheafHom_naturality_source X T f M
  have hsum : ∀ (H : (DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) [H.Additive],
      ∑ k ∈ s, H.map (r k ≫ i k).op = 𝟙 (H.obj (op L)) := fun H _ => by
    rw [← Functor.map_sum, ← op_sum, hir, op_id, CategoryTheory.Functor.map_id]
  refine ⟨∑ k ∈ s, G.map (i k).op ≫
      (@inv _ _ _ _ (derivedTensorDualToSheafHom X T (L' k) M) (h k)) ≫ F.map (r k).op, ?_, ?_⟩
  · rw [Preadditive.comp_sum]
    refine (Finset.sum_congr rfl fun k _ => ?_).trans (hsum F)
    have := h k
    rw [← Category.assoc, ← hnat (i k), Category.assoc, IsIso.hom_inv_id_assoc,
      ← Functor.map_comp, ← op_comp]
  · rw [Preadditive.sum_comp]
    refine (Finset.sum_congr rfl fun k _ => ?_).trans (hsum G)
    have := h k
    rw [Category.assoc, Category.assoc, hnat (r k), IsIso.inv_hom_id_assoc,
      ← Functor.map_comp, ← op_comp]

/-- **The canonical map of Stacks 08JD is invertible at a retract of an object at which it is
invertible** — that is, at a direct summand in `D(O)`.

A retract datum `i : L ⟶ L'`, `r : L' ⟶ L` with `i ≫ r = 𝟙` induces, by the contravariant
functoriality of the canonical map, a retract of the arrow `Φ_{L'}` onto the arrow `Φ_L`; the
inverse of `Φ_L` is then `RSheafHom(r, M)` followed by the inverse of `Φ_{L'}` followed by the
map induced by `RSheafHom(i, O)`. -/
theorem isIso_derivedTensorDualToSheafHom_of_retract
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (i : L ⟶ L') (r : L' ⟶ L) (hir : i ≫ r = 𝟙 L)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : IsIso (derivedTensorDualToSheafHom X T L' M)) :
    IsIso (derivedTensorDualToSheafHom X T L M) :=
  isIso_derivedTensorDualToSheafHom_of_sum_id_aux X T (Finset.univ : Finset Unit)
    (fun _ => r) (fun _ => i) (by simpa using hir) M fun _ => h

/-- **The canonical map of Stacks 08JD is invertible at a target as soon as it is invertible at
an isomorphic one.** The two canonical maps are intertwined by the map induced on the tensor
factor and by the map induced on the internal Homs, and both of those are invertible. -/
theorem isIso_derivedTensorDualToSheafHom_of_iso_target
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : M ≅ M')
    (h : IsIso (derivedTensorDualToSheafHom X T L M')) :
    IsIso (derivedTensorDualToSheafHom X T L M) := by
  have he : IsIso e.hom := e.isIso_hom
  have hsource : IsIso ((T.tensor.map e.hom).app (derivedDual X L)) := inferInstance
  have key := derivedTensorDualToSheafHom_naturality X T L e.hom
  have hrhs : IsIso ((T.tensor.map e.hom).app (derivedDual X L) ≫
      derivedTensorDualToSheafHom X T L M') := by
    have := h
    infer_instance
  rw [key] at hrhs
  exact IsIso.of_isIso_comp_right (derivedTensorDualToSheafHom X T L M)
    (((derivedSheafHomBifunctor X).obj (op L)).map e.hom)

/-- **The canonical map of Stacks 08JD is invertible at a zero target.** Both its source and its
target are zero: `RSheafHom(L, -)` is additive and `- ⊗^L_O L^∨` is triangulated, hence additive,
so each carries a zero object to a zero object. -/
theorem isIso_derivedTensorDualToSheafHom_of_isZero_target
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hM : IsZero M) :
    IsIso (derivedTensorDualToSheafHom X T L M) := by
  have htarget : IsZero (((derivedSheafHomBifunctor X).obj (op L)).obj M) :=
    Functor.map_isZero ((derivedSheafHomBifunctor X).obj (op L)) hM
  have hsource : IsZero ((T.tensor.obj M).obj (derivedDual X L)) :=
    Functor.map_isZero (T.tensor.flip.obj (derivedDual X L)) hM
  exact hsource.isIso htarget _

/-- The source of the canonical map of Stacks 08JD, as a contravariant functor of the dualized
object: the derived dual followed by the derived tensor product with `M`. -/
abbrev tensorDualSourceFunctor (M : DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X) ⋙ T.tensor.obj M

/-- **The canonical map of Stacks 08JD is invertible at a direct summand of a finite direct sum
of objects at which it is invertible.** The hypothesis is the decomposition of the identity of
`L` as a finite sum `∑ k ∈ s, r k ≫ i k` through objects `L' k` at which the map is invertible,
which is exactly what exhibits `L` as such a summand.

Both the source `M ⊗^L_O (-)^∨` and the target `RSheafHom(-, M)` of the canonical map are
additive contravariant functors of the dualized object, and the canonical map is a natural
transformation between them. So the sum `∑ k ∈ s, RSheafHom(i k, M)` followed by the inverse at
`L' k` followed by the map induced on the duals by `r k` is a two-sided inverse: each composite
telescopes by naturality to the image of `∑ k ∈ s, r k ≫ i k = 𝟙 L` under one of the two
functors.

This is a dévissage step of the proof of Stacks 08JJ; see the section "What this file does not
contain" of this file. -/
theorem isIso_derivedTensorDualToSheafHom_of_sum_id
    {ι : Type*} (s : Finset ι)
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {L' : ι → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (i : ∀ k, L' k ⟶ L) (r : ∀ k, L ⟶ L' k)
    (hir : ∑ k ∈ s, r k ≫ i k = 𝟙 L)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ k, IsIso (derivedTensorDualToSheafHom X T (L' k) M)) :
    IsIso (derivedTensorDualToSheafHom X T L M) :=
  isIso_derivedTensorDualToSheafHom_of_sum_id_aux X T s i r hir M h

/-- **The canonical map of Stacks 08JD is invertible at a finite direct sum of objects at which
it is invertible.** The identity of `⨁ L` is the sum of the composites of its projections with
its inclusions, so this is the previous statement at that decomposition. -/
theorem isIso_derivedTensorDualToSheafHom_of_biproduct
    {ι : Type} [Finite ι]
    (L : ι → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasBiproduct L]
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ k, IsIso (derivedTensorDualToSheafHom X T (L k) M)) :
    IsIso (derivedTensorDualToSheafHom X T (⨁ L) M) := by
  let := Fintype.ofFinite ι
  exact isIso_derivedTensorDualToSheafHom_of_sum_id X T Finset.univ
    (fun k => biproduct.ι L k) (fun k => biproduct.π L k) biproduct.total M h

end AlgebraicGeometry.RingedSite

end
