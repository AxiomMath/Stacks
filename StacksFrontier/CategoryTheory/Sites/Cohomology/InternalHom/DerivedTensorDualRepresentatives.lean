module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map `M ⊗^L L^∨ ⟶ RSheafHom(L, M)` on representatives

Let `(C, O)` be a ringed site. **Stacks 08JD** supplies the canonical map

`Φ_{L,M} : M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)`,

`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom`. This file computes it on
representatives: for a complex `E`, a K-injective complex `I` and a K-flat complex `H` mapping
to the internal Hom complex `SheafHom(E, J)` — where `J` is a K-injective resolution of the
structure sheaf — the map `Φ_{Q E, Q I}`, read through the comparisons, is the class of the
composition morphism of internal Hom complexes of Stacks 0A91.

This is the first of the two inputs that the sections "What this file does not contain" of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals`,
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing` record as missing for the
third assertion of Stacks 08JJ; the second, the compatibility of `Φ` with restriction to a
slice, is still absent — see "What this file does not contain" below.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorDualSourceComparison`: the comparison
  `RSheafHom(QJ, QI) ⊗^L_O Q H ⟶ Q I ⊗^L_O (Q E)^∨` assembled from a K-injective resolution
  `g : O[0] ⟶ J` of the structure sheaf and a morphism `f : H ⟶ SheafHom(E, J)`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_comp_eq`: the canonical map,
  preceded by that comparison, is derived composition at intermediate object `Q J`, preceded by
  the map induced by `f`.
* `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_kFlatModel`: **the canonical map of
  Stacks 08JD on a K-flat model.** Read through the comparisons it is the class of
  `Tot(SheafHom(J, I) ⊗_O H) ⟶ SheafHom(E, I)`, the composition morphism of Stacks 0A91
  precomposed with `f` in its second tensor factor.

## Implementation notes

The canonical map of Stacks 08JD is derived composition of Stacks 0A98 at intermediate object
the structure sheaf, after the identification `M ≅ RSheafHom(O, M)`. The K-flat computation of
Stacks 0A98, `AlgebraicGeometry.RingedSite.derivedSheafHomComposition_kFlatModel`, is stated
with the intermediate object the class of a **K-injective** complex, and the structure sheaf
complex is not K-injective. The intermediate object is therefore moved by the dinaturality of
Stacks 0A98 along the class of a K-injective resolution `g : O[0] ⟶ J`, which is an isomorphism
of `D(O)`; that is the whole content of `derivedTensorDualToSheafHom_comp_eq`, and the K-flat
computation is then applied verbatim.

Both statements are made for an arbitrary morphism `f : H ⟶ SheafHom(E, J)` out of a K-flat
complex, with no quasi-isomorphism hypothesis, exactly as
`derivedSheafHomComposition_kFlatModel` is: the identity holds for every such `f`, and the
K-flatness of `H` enters only through the source comparison
`AlgebraicGeometry.RingedSite.derivedEvaluationSourceComparison`.

The derived internal Hom datum is **instantiated** at
`AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor`, as it must be: the identification
`RSheafHom(O, -) ≅ 𝟭` that `derivedTensorDualToSheafHom` is built from is stated for the
bifunctor `RSheafHom(-, -)` itself. The derived tensor product datum is carried as a parameter,
as in `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual`.

The universes are the diagonal `RingedSite.{u, u, u}` with the standard derived category, as in
every file of the derived internal Hom cluster.

## What this file does not contain

No assertion of Stacks 08JJ is proved here, and no `@[stacks]` attribute is attached. What is
below is a computation of the canonical map of Stacks 08JD on representatives; Stacks 08JD
asserts only that the map exists, and Stacks 0A98, whose K-flat computation this transports,
likewise. The third assertion of Stacks 08JJ — the isomorphism
`M ⊗^L_O K^∨ ≅ RSheafHom_O(K, M)` for perfect `K` — is in the library, as
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom`, but by a different
route: the diagonal of Stacks 0BYS at target object the structure sheaf, invertible by
Stacks 0ATN. The invertibility of the *canonical* map `Φ` of Stacks 08JD **is** in the
library, as
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHomCanonical`, and the
K-flat computation below is one of its two inputs: the other is the computation of the
diagonal of Stacks 0BYS at the same models, and the two chain-level morphisms are compared
over the roof `Tot(A ⊗_O H)`.

Three things are not needed for that invertibility
— the identification of `compositionMap` with the module-level map of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorDualSheafHom`, the compatibility of `Φ`
with restriction to a slice, and a K-injective resolution of the structure sheaf whose internal
Hom complexes out of a strictly perfect complex are computed. Those are the inputs of the
*source's* local argument, which is not the route taken: comparing `Φ` with the diagonal of
Stacks 0BYS transports the locality that Stacks 0ATN has already carried out.

## References

* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

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

variable
  (E J I H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  [J.IsKInjective] [I.IsKInjective]
  (g : structureSheafComplex X ⟶ J) [IsIso (DerivedCategory.Q.map g)]
  (f : H ⟶ (sheafHomComplex X E J).obj)

/-- The comparison identifying the source of the K-flat computation of Stacks 0A98 at
intermediate object `Q J` with the source of the canonical map of Stacks 08JD at `Q E` and
`Q I`.

Its left tensor factor is the class of `g` read on internal Homs, `RSheafHom(QJ, QI) ⟶
RSheafHom(O, QI)`, followed by the identification `RSheafHom(O, QI) ≅ QI` of
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`; its right tensor factor is `f`,
followed by the K-injective model comparison and by the inverse of the class of `g` read on
internal Homs out of `Q E`. -/
def derivedTensorDualSourceComparison :
    (T.tensor.obj (((derivedInternalHomOfBifunctor X).hom.obj
          (op (DerivedCategory.Q.obj J))).obj (DerivedCategory.Q.obj I))).obj
        (DerivedCategory.Q.obj H) ⟶
      (T.tensor.obj (DerivedCategory.Q.obj I)).obj
        (derivedDual X (DerivedCategory.Q.obj E)) :=
  derivedTensorMap X T
    (((derivedInternalHomOfBifunctor X).hom.map (DerivedCategory.Q.map g).op).app
        (DerivedCategory.Q.obj I) ≫
      (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom)
    (DerivedCategory.Q.map f ≫ ((derivedInternalHomOfBifunctor X).homComparison E J).inv ≫
      ((derivedInternalHomOfBifunctor X).hom.obj
        (op (DerivedCategory.Q.obj E))).map (inv (DerivedCategory.Q.map g)))

omit [I.IsKInjective] in
/-- **The canonical map of Stacks 08JD is derived composition at the intermediate object `Q J`.**
Preceded by `derivedTensorDualSourceComparison`, the canonical map of Stacks 08JD at `Q E` and
`Q I` is the composition morphism of Stacks 0A98 at intermediate object `Q J`, preceded by the
map induced on the right tensor factor by `f` and the K-injective model comparison.

The two differ only in the intermediate object, and the class of the resolution `g` is an
isomorphism, so this is the dinaturality of Stacks 0A98 in the intermediate object together
with the two naturality squares of the tensor product. -/
theorem derivedTensorDualToSheafHom_comp_eq :
    derivedTensorDualSourceComparison X T E J I H g f ≫
        derivedTensorDualToSheafHom X T (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj I) =
      (T.tensor.obj (((derivedInternalHomOfBifunctor X).hom.obj
              (op (DerivedCategory.Q.obj J))).obj (DerivedCategory.Q.obj I))).map
          (DerivedCategory.Q.map f ≫
            ((derivedInternalHomOfBifunctor X).homComparison E J).inv) ≫
        derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X)
          (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I) := by
  -- `vg` moves the left tensor factor from `RSheafHom(QJ, QI)` to `RSheafHom(O, QI)`, `ug`
  -- moves the dual from `RSheafHom(QE, O)` to `RSheafHom(QE, QJ)`, and `b` is `f` read on the
  -- dual. Every auxiliary identity is stated at the spelling the unfolded goal uses.
  have huiso : IsIso (((derivedSheafHomBifunctor X).obj
      (op (DerivedCategory.Q.obj E))).map (DerivedCategory.Q.map g)) := Functor.map_isIso _ _
  have huinv : ((derivedSheafHomBifunctor X).obj
        (op (DerivedCategory.Q.obj E))).map (inv (DerivedCategory.Q.map g)) =
      inv (((derivedSheafHomBifunctor X).obj
        (op (DerivedCategory.Q.obj E))).map (DerivedCategory.Q.map g)) :=
    Functor.map_inv _ _
  have hdin := derivedSheafHomComposition_dinatural_middle X T
    (derivedInternalHomOfBifunctor X) (DerivedCategory.Q.obj E) (DerivedCategory.Q.map g)
    (DerivedCategory.Q.obj I)
  simp only [derivedTensorMap, derivedSheafHomMap, derivedInternalHomOfBifunctor_hom, op_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id] at hdin
  have hnatv := (T.tensor.map (((derivedSheafHomBifunctor X).map
      (DerivedCategory.Q.map g).op).app (DerivedCategory.Q.obj I))).naturality
      (DerivedCategory.Q.map f ≫ (derivedSheafHomComparison X E J).inv ≫
        inv (((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj E))).map (DerivedCategory.Q.map g)))
  have hnatι := (T.tensor.map (derivedStructureSheafHomIso X
      (DerivedCategory.Q.obj I)).inv).naturality
      (DerivedCategory.Q.map f ≫ (derivedSheafHomComparison X E J).inv ≫
        inv (((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj E))).map (DerivedCategory.Q.map g)))
  have hmerge : (T.tensor.map (((derivedSheafHomBifunctor X).map
            (DerivedCategory.Q.map g).op).app (DerivedCategory.Q.obj I) ≫
          (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom)).app
          (DerivedCategory.Q.obj H) ≫
        (T.tensor.map (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).inv).app
          (DerivedCategory.Q.obj H) =
      (T.tensor.map (((derivedSheafHomBifunctor X).map
        (DerivedCategory.Q.map g).op).app (DerivedCategory.Q.obj I))).app
        (DerivedCategory.Q.obj H) := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  dsimp only [derivedTensorDualSourceComparison, derivedTensorMap, derivedTensorDualToSheafHom,
    derivedDual, derivedStructureSheaf]
  rw [huinv]
  simp only [Category.assoc]
  rw [reassoc_of% hnatι, reassoc_of% hmerge, ← reassoc_of% hnatv, ← hdin, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  simp

/-- **The canonical map of Stacks 08JD on a K-flat model.** Let `E` be a complex, `J` a
K-injective resolution of the structure sheaf, `I` a K-injective complex, `H` a K-flat complex
and `f : H ⟶ SheafHom(E, J)` *any* morphism. Then the canonical map

`Φ : Q I ⊗^L_O (Q E)^∨ ⟶ RSheafHom(Q E, Q I)`

of Stacks 08JD, read through `derivedTensorDualSourceComparison` on the source and through the
K-injective model comparison on the target, is the class of the composition morphism of
internal Hom complexes of Stacks 0A91, precomposed with `f` in its second tensor factor.

This is `AlgebraicGeometry.RingedSite.derivedSheafHomComposition_kFlatModel`, the K-flat
computation of Stacks 0A98, transported to the intermediate object the structure sheaf by
`derivedTensorDualToSheafHom_comp_eq`. -/
theorem derivedTensorDualToSheafHom_kFlatModel
    (hH : Stacks.SheafOfModules.IsKFlat X.O H) :
    derivedTensorDualSourceComparison X T E J I H g f ≫
        derivedTensorDualToSheafHom X T (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj I) ≫
        ((derivedInternalHomOfBifunctor X).homComparison E I).hom =
      (derivedEvaluationSourceComparison X T (derivedInternalHomOfBifunctor X) H J I hH).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f) ≫
        DerivedCategory.Q.map (compositionMap X E J I) := by
  rw [← derivedSheafHomComposition_kFlatModel X T (derivedInternalHomOfBifunctor X) E J I H hH f,
    ← Category.assoc, ← Category.assoc, derivedTensorDualToSheafHom_comp_eq]

end AlgebraicGeometry.RingedSite

end
