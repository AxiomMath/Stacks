module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.KFlat.Basic

/-!
# Monoidal coherence for the derived tensor--Hom adjunction

`StacksDraft.DerivedHom.DerivedHomAdjunction` packages the derived tensor product and derived
Hom bifunctors on `D(R)` together with an associator, a symmetry and the natural Hom
equivalence, but it records no coherence between them: neither the unitor triangle nor the
braiding hexagon is a field. Those two identities are what the duality computations of
Stacks 47 reduce to once the Hom equivalence has been applied, so this module proves them.

Both identities are proved on *models*. On K-flat representatives the derived associator,
symmetry and left unitor are the associator, braiding and left unitor of the genuine symmetric
monoidal category `CochainComplex (ModuleCat R) ℤ` with the Koszul sign convention, so the
chain-level coherence laws of Mathlib apply; both sides of each identity are natural, and every
object of `D(R)` is represented by a K-flat complex, so the identity at representatives extends
to all objects.

## Main definitions

* `DerivedHomAdjunction.IsUnitorNatural`, `DerivedHomAdjunction.IsUnitorTriangleAt`: naturality
  of a left unitor for a chosen tensor unit, and the left-unitor/associator triangle at a pair
  of objects.
* `DerivedHomAdjunction.IsTensorHexagonAt`: the braiding hexagon at a triple of objects.
* `DerivedHomAdjunction.transportUnitorLeft`: a left unitor for an adjunction transported along
  an additive equivalence of derived categories.
* `derivedTensorUnit`, `derivedTensorUnitLeft`: the tensor unit and left unitor of
  `derivedHomAdjunctionOverRing`, which carries neither of its own.
* `DerivedHomAdjunction.TransportIso`: an isomorphism of derived tensor--Hom adjunctions along an
  additive equivalence of derived categories -- comparison isomorphisms of both bifunctors
  together with the compatibility of the two Hom equivalences.
* `DerivedHomAdjunction.transportIso`: `DerivedHomAdjunction.transport` is such an isomorphism.
* `DerivedHomAdjunction.TransportIso.homEquiv_symm_comparison`,
  `DerivedHomAdjunction.TransportIso.evaluation_comparison`: transposition in the inverse
  direction, and the evaluation morphism, cross such an isomorphism.
* `derivedHomAdjunctionOverRingIso`: the scalar bridge, identifying
  `derivedHomAdjunctionOverRing R` with the model-level adjunction over `ULift.{v} R` transported
  along `derivedScalarEquivalence`.

## Main results

* `derivedHomAdjunction_unitorTriangle`, `derivedHomAdjunction_tensorHexagon`: the triangle and
  the hexagon for the canonical model-level adjunction `derivedHomAdjunction`, at arbitrary
  objects of `D(R)`.
* `derivedTensorUnitLeft_triangle`, `derivedHomAdjunctionOverRing_tensorHexagon`: the same two
  identities for `derivedHomAdjunctionOverRing`, the adjunction appearing in the tagged
  statement of [stacks 0A63].
* `DerivedHomAdjunction.isUnitorTriangleAt_of_iso`,
  `DerivedHomAdjunction.isTensorHexagonAt_of_iso`: both identities are natural, hence stable
  under isomorphisms in each variable.
* `DerivedHomAdjunction.isUnitorTriangleAt_transport`,
  `DerivedHomAdjunction.isTensorHexagonAt_transport`: both identities transport along an
  additive equivalence of derived categories, which is how they reach
  `derivedHomAdjunctionOverRing`.
* `derivedInternalHom_eq`: the two library spellings of the derived internal-Hom bifunctor,
  `Stacks.DerivedHom.ScalarTransportedInternalHom.hom` and `(derivedHomAdjunctionOverRing _).hom`,
    are the same
  functor.
* `DerivedHomAdjunction.transportHomEquiv_map`: the Hom equivalence of a transported adjunction is
  the original one conjugated by the two comparison isomorphisms the transport already carries.
* `derivedHomAdjunctionULift_hom_eq`, `derivedHomAdjunctionULift_tensor_eq`,
  `derivedHomAdjunctionULift_homEquiv_eq`: the lifted model-level adjunction is the canonical
  `DerivedInternalHom.Model` data over `ULift.{v} R`.
* `modelHomEquiv_homInternalHomEquiv`, `modelHomEquiv_symm_homInternalHomEquiv_symm`: the scalar
  bridge at the level of transposition, in both directions.
* `exists_kFlat_representative`: every object of `D(R)` is isomorphic to the image of a K-flat
  complex.

## Implementation notes

The coherence identities are not fields of `DerivedHomAdjunction`, and adding them there would
change a structure with many consumers, so they are stated as standalone propositions
`IsUnitorTriangleAt` and `IsTensorHexagonAt` parameterized by the adjunction (and, for the
triangle, by a choice of tensor unit and left unitor, since `DerivedHomAdjunction` has no unit
either). `DerivedHomData.tensorUnitLeft` supplies the unitor on the model side;
`transportUnitorLeft` carries it across `DerivedHomAdjunction.transport`, and
`derivedTensorUnitLeft` is the resulting unitor for `derivedHomAdjunctionOverRing`.

The derived-Hom bifunctor is reached in the library by two different constants:
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom R`, which restricts scalars to `ULift R` and
  back along
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`, and
`(derivedHomAdjunctionOverRing R).hom`, which transports along `derivedScalarEquivalence`, the
opposite spelling of the same equivalence. `derivedInternalHom_eq` records that these two
constants are in fact *equal*: the two scalar equivalences have the same functor and the same
inverse, swapped, and the internal-Hom bifunctor uses only those, not the unit and counit
isomorphisms (which do differ). So every result stated for either spelling can be rewritten
into the other, and the results of this module apply to both.

Neither of those two constants is `DerivedInternalHom.Model.hom R`: the model API needs the
module universe to equal the ring universe, which is what forces the detour through `ULift.{v} R`
in the first place. The two vocabularies therefore meet over the *lifted* ring, where the module
universe `max u v` is the ring's own: `derivedHomAdjunctionULift_hom_eq` identifies the Hom half
of the lifted adjunction with `DerivedInternalHom.Model.hom (ULift.{v} R)`, so the comparison
`derivedHomULiftIso` already is the comparison of the model bifunctor over `ULift.{v} R` with
derived internal Hom over `R`. What `DerivedHomAdjunction.transport` does not record is that this
comparison is compatible with the two Hom equivalences -- it keeps only the three fields of
`DerivedHomAdjunction` and drops every concrete comparison field of `DerivedHomData`, and it must,
since those fields are stated on `Model.Complex S`, which does not exist at a module universe
different from the ring's. `DerivedHomAdjunction.TransportIso` is the datum that is missing, and
`DerivedHomAdjunction.transportIso` supplies it from the three structure fields alone; the result
for the scalar transport is `derivedHomAdjunctionOverRingIso`.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0795](https://stacks.math.columbia.edu/tag/0795)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace StacksDraft.DerivedHom

universe u v w

namespace DerivedHomAdjunction

section Abstract

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R) (one : DerivedCategory (ModuleCat.{v} R))
  (lam : ∀ K : DerivedCategory (ModuleCat.{v} R), d.tensor.obj (one, K) ≅ K)

/-- Naturality of a candidate left unitor `lam` for the tensor unit `one`: tensoring a morphism
with the identity of the unit on the left commutes with `lam`. -/
public def IsUnitorNatural : Prop :=
  ∀ {K K' : DerivedCategory (ModuleCat.{v} R)} (f : K ⟶ K'),
    d.tensor.map (show (one, K) ⟶ (one, K') from (𝟙 one, f)) ≫ (lam K').hom = (lam K).hom ≫ f

/-- The left-unitor/associator triangle at a pair of objects: associating `(1 ⊗ K) ⊗ X` and then
removing the unit agrees with removing the unit in the left factor. -/
public def IsUnitorTriangleAt (K X : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  (d.tensorAssoc one K X).hom ≫ (lam (d.tensor.obj (K, X))).hom =
    d.tensor.map (show (d.tensor.obj (one, K), X) ⟶ (K, X) from ((lam K).hom, 𝟙 X))

/-- The braiding hexagon at a triple of objects: moving `X` past `Y ⊗ Z` in one step agrees with
moving it past `Y` and then past `Z`. -/
public def IsTensorHexagonAt (X Y Z : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  (d.tensorAssoc X Y Z).hom ≫ (d.tensorSwap X (d.tensor.obj (Y, Z))).hom ≫
      (d.tensorAssoc Y Z X).hom =
    d.tensor.map (show (d.tensor.obj (X, Y), Z) ⟶ (d.tensor.obj (Y, X), Z) from
        ((d.tensorSwap X Y).hom, 𝟙 Z)) ≫
      (d.tensorAssoc Y X Z).hom ≫
      d.tensor.map (show (Y, d.tensor.obj (X, Z)) ⟶ (Y, d.tensor.obj (Z, X)) from
        (𝟙 Y, (d.tensorSwap X Z).hom))

/-- Splitting a composite in the left slot of a tensored morphism. -/
public theorem tensor_map_fst_comp {A B C : DerivedCategory (ModuleCat.{v} R)}
    (f : A ⟶ B) (g : B ⟶ C) (W : DerivedCategory (ModuleCat.{v} R)) :
    d.tensor.map (show (A, W) ⟶ (C, W) from (f ≫ g, 𝟙 W)) =
      d.tensor.map (show (A, W) ⟶ (B, W) from (f, 𝟙 W)) ≫
        d.tensor.map (show (B, W) ⟶ (C, W) from (g, 𝟙 W)) := by
  rw [d.tensor_map_comp, Category.comp_id]

/-- Splitting a composite in the right slot of a tensored morphism. -/
public theorem tensor_map_snd_comp (W : DerivedCategory (ModuleCat.{v} R))
    {A B C : DerivedCategory (ModuleCat.{v} R)} (f : A ⟶ B) (g : B ⟶ C) :
    d.tensor.map (show (W, A) ⟶ (W, C) from (𝟙 W, f ≫ g)) =
      d.tensor.map (show (W, A) ⟶ (W, B) from (𝟙 W, f)) ≫
        d.tensor.map (show (W, B) ⟶ (W, C) from (𝟙 W, g)) := by
  rw [d.tensor_map_comp, Category.comp_id]

/-- A tensored morphism is a morphism in the left slot followed by one in the right slot. -/
private theorem tensor_map_eq_fst_comp_snd {A B C D : DerivedCategory (ModuleCat.{v} R)}
    (f : A ⟶ B) (g : C ⟶ D) :
    d.tensor.map (show (A, C) ⟶ (B, D) from (f, g)) =
      d.tensor.map (show (A, C) ⟶ (B, C) from (f, 𝟙 C)) ≫
        d.tensor.map (show (B, C) ⟶ (B, D) from (𝟙 B, g)) := by
  rw [d.tensor_map_comp]
  simp

/-- A retraction in the left slot of a tensored morphism stays a retraction. -/
public theorem tensor_map_fst_comp_eq_id {A B : DerivedCategory (ModuleCat.{v} R)}
    (f : A ⟶ B) (g : B ⟶ A) (hfg : f ≫ g = 𝟙 A) (W : DerivedCategory (ModuleCat.{v} R)) :
    d.tensor.map (show (A, W) ⟶ (B, W) from (f, 𝟙 W)) ≫
      d.tensor.map (show (B, W) ⟶ (A, W) from (g, 𝟙 W)) = 𝟙 (d.tensor.obj (A, W)) := by
  rw [d.tensor_map_comp, Category.comp_id, hfg, d.tensor_map_id]

/-- A retraction in the right slot of a tensored morphism stays a retraction. -/
public theorem tensor_map_snd_comp_eq_id (W : DerivedCategory (ModuleCat.{v} R))
    {A B : DerivedCategory (ModuleCat.{v} R)} (f : A ⟶ B) (g : B ⟶ A) (hfg : f ≫ g = 𝟙 A) :
    d.tensor.map (show (W, A) ⟶ (W, B) from (𝟙 W, f)) ≫
      d.tensor.map (show (W, B) ⟶ (W, A) from (𝟙 W, g)) = 𝟙 (d.tensor.obj (W, A)) := by
  rw [d.tensor_map_comp, Category.comp_id, hfg, d.tensor_map_id]

variable {d}

/-- The tensor bifunctor sends a pair of isomorphisms to an isomorphism. -/
public theorem isIso_tensor_map {A B C D : DerivedCategory (ModuleCat.{v} R)}
    (f : A ⟶ B) (g : C ⟶ D) [IsIso f] [IsIso g] :
    IsIso (d.tensor.map (show (A, C) ⟶ (B, D) from (f, g))) := by
  have : IsIso (show (A, C) ⟶ (B, D) from (f, g)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  infer_instance

variable {one lam}

/-- The left-hand side of the unitor triangle is natural in both variables. -/
private theorem unitorTriangle_lhs_naturality (hlam : IsUnitorNatural d one lam)
    {K K' X X' : DerivedCategory (ModuleCat.{v} R)} (f : K' ⟶ K) (g : X' ⟶ X) :
    d.tensor.map (show (d.tensor.obj (one, K'), X') ⟶ (d.tensor.obj (one, K), X) from
        (d.tensor.map (show (one, K') ⟶ (one, K) from (𝟙 one, f)), g)) ≫
      (d.tensorAssoc one K X).hom ≫ (lam (d.tensor.obj (K, X))).hom =
    ((d.tensorAssoc one K' X').hom ≫ (lam (d.tensor.obj (K', X'))).hom) ≫
      d.tensor.map (show (K', X') ⟶ (K, X) from (f, g)) := by
  rw [d.tensorAssoc_naturality_assoc,
    hlam (d.tensor.map (show (K', X') ⟶ (K, X) from (f, g))), Category.assoc]

/-- The right-hand side of the unitor triangle is natural in both variables. -/
private theorem unitorTriangle_rhs_naturality (hlam : IsUnitorNatural d one lam)
    {K K' X X' : DerivedCategory (ModuleCat.{v} R)} (f : K' ⟶ K) (g : X' ⟶ X) :
    d.tensor.map (show (d.tensor.obj (one, K'), X') ⟶ (d.tensor.obj (one, K), X) from
        (d.tensor.map (show (one, K') ⟶ (one, K) from (𝟙 one, f)), g)) ≫
      d.tensor.map (show (d.tensor.obj (one, K), X) ⟶ (K, X) from ((lam K).hom, 𝟙 X)) =
    d.tensor.map (show (d.tensor.obj (one, K'), X') ⟶ (K', X') from ((lam K').hom, 𝟙 X')) ≫
      d.tensor.map (show (K', X') ⟶ (K, X) from (f, g)) := by
  rw [d.tensor_map_comp, d.tensor_map_comp, Category.comp_id, Category.id_comp, hlam f]

/-- Both sides of the unitor triangle are natural, so the triangle transports along
isomorphisms in each variable. -/
public theorem isUnitorTriangleAt_of_iso (hlam : IsUnitorNatural d one lam)
    {K K' X X' : DerivedCategory (ModuleCat.{v} R)} (eK : K' ≅ K) (eX : X' ≅ X)
    (h : IsUnitorTriangleAt d one lam K' X') : IsUnitorTriangleAt d one lam K X := by
  have : IsIso (d.tensor.map (show (one, K') ⟶ (one, K) from (𝟙 one, eK.hom))) :=
    isIso_tensor_map (d := d) (𝟙 one) eK.hom
  have := isIso_tensor_map (d := d)
    (d.tensor.map (show (one, K') ⟶ (one, K) from (𝟙 one, eK.hom))) eX.hom
  rw [IsUnitorTriangleAt, ← cancel_epi (d.tensor.map (show
    (d.tensor.obj (one, K'), X') ⟶ (d.tensor.obj (one, K), X) from
    (d.tensor.map (show (one, K') ⟶ (one, K) from (𝟙 one, eK.hom)), eX.hom))),
    unitorTriangle_lhs_naturality hlam, unitorTriangle_rhs_naturality hlam, h]

/-- The left-hand side of the hexagon is natural in all three variables. -/
private theorem tensorHexagon_lhs_naturality
    {X X' Y Y' Z Z' : DerivedCategory (ModuleCat.{v} R)}
    (f : X' ⟶ X) (g : Y' ⟶ Y) (h : Z' ⟶ Z) :
    d.tensor.map (show (d.tensor.obj (X', Y'), Z') ⟶ (d.tensor.obj (X, Y), Z) from
        (d.tensor.map (show (X', Y') ⟶ (X, Y) from (f, g)), h)) ≫
      (d.tensorAssoc X Y Z).hom ≫ (d.tensorSwap X (d.tensor.obj (Y, Z))).hom ≫
        (d.tensorAssoc Y Z X).hom =
    ((d.tensorAssoc X' Y' Z').hom ≫ (d.tensorSwap X' (d.tensor.obj (Y', Z'))).hom ≫
        (d.tensorAssoc Y' Z' X').hom) ≫
      d.tensor.map (show (Y', d.tensor.obj (Z', X')) ⟶ (Y, d.tensor.obj (Z, X)) from
        (g, d.tensor.map (show (Z', X') ⟶ (Z, X) from (h, f)))) := by
  rw [d.tensorAssoc_naturality_assoc, d.tensorSwap_naturality_assoc,
    d.tensorAssoc_naturality]
  simp only [Category.assoc]

/-- The right-hand side of the hexagon is natural in all three variables. -/
private theorem tensorHexagon_rhs_naturality
    {X X' Y Y' Z Z' : DerivedCategory (ModuleCat.{v} R)}
    (f : X' ⟶ X) (g : Y' ⟶ Y) (h : Z' ⟶ Z) :
    d.tensor.map (show (d.tensor.obj (X', Y'), Z') ⟶ (d.tensor.obj (X, Y), Z) from
        (d.tensor.map (show (X', Y') ⟶ (X, Y) from (f, g)), h)) ≫
      (d.tensor.map (show (d.tensor.obj (X, Y), Z) ⟶ (d.tensor.obj (Y, X), Z) from
          ((d.tensorSwap X Y).hom, 𝟙 Z)) ≫
        (d.tensorAssoc Y X Z).hom ≫
        d.tensor.map (show (Y, d.tensor.obj (X, Z)) ⟶ (Y, d.tensor.obj (Z, X)) from
          (𝟙 Y, (d.tensorSwap X Z).hom))) =
    (d.tensor.map (show (d.tensor.obj (X', Y'), Z') ⟶ (d.tensor.obj (Y', X'), Z') from
        ((d.tensorSwap X' Y').hom, 𝟙 Z')) ≫
      (d.tensorAssoc Y' X' Z').hom ≫
      d.tensor.map (show (Y', d.tensor.obj (X', Z')) ⟶ (Y', d.tensor.obj (Z', X')) from
        (𝟙 Y', (d.tensorSwap X' Z').hom))) ≫
      d.tensor.map (show (Y', d.tensor.obj (Z', X')) ⟶ (Y, d.tensor.obj (Z, X)) from
        (g, d.tensor.map (show (Z', X') ⟶ (Z, X) from (h, f)))) := by
  have h1 : d.tensor.map (show (d.tensor.obj (X', Y'), Z') ⟶ (d.tensor.obj (X, Y), Z) from
        (d.tensor.map (show (X', Y') ⟶ (X, Y) from (f, g)), h)) ≫
      d.tensor.map (show (d.tensor.obj (X, Y), Z) ⟶ (d.tensor.obj (Y, X), Z) from
        ((d.tensorSwap X Y).hom, 𝟙 Z)) =
      d.tensor.map (show (d.tensor.obj (X', Y'), Z') ⟶ (d.tensor.obj (Y', X'), Z') from
          ((d.tensorSwap X' Y').hom, 𝟙 Z')) ≫
        d.tensor.map (show (d.tensor.obj (Y', X'), Z') ⟶ (d.tensor.obj (Y, X), Z) from
          (d.tensor.map (show (Y', X') ⟶ (Y, X) from (g, f)), h)) := by
    rw [d.tensor_map_comp, d.tensor_map_comp, Category.comp_id, Category.id_comp,
      d.tensorSwap_naturality]
  have h2 : d.tensor.map (show (Y', d.tensor.obj (X', Z')) ⟶ (Y, d.tensor.obj (X, Z)) from
        (g, d.tensor.map (show (X', Z') ⟶ (X, Z) from (f, h)))) ≫
      d.tensor.map (show (Y, d.tensor.obj (X, Z)) ⟶ (Y, d.tensor.obj (Z, X)) from
        (𝟙 Y, (d.tensorSwap X Z).hom)) =
      d.tensor.map (show (Y', d.tensor.obj (X', Z')) ⟶ (Y', d.tensor.obj (Z', X')) from
          (𝟙 Y', (d.tensorSwap X' Z').hom)) ≫
        d.tensor.map (show (Y', d.tensor.obj (Z', X')) ⟶ (Y, d.tensor.obj (Z, X)) from
          (g, d.tensor.map (show (Z', X') ⟶ (Z, X) from (h, f)))) := by
    rw [d.tensor_map_comp, d.tensor_map_comp, Category.comp_id, Category.id_comp,
      d.tensorSwap_naturality]
  rw [reassoc_of% h1, d.tensorAssoc_naturality_assoc, h2]
  simp only [Category.assoc]

/-- Both sides of the hexagon are natural, so it transports along isomorphisms in each
variable. -/
public theorem isTensorHexagonAt_of_iso {X X' Y Y' Z Z' : DerivedCategory (ModuleCat.{v} R)}
    (eX : X' ≅ X) (eY : Y' ≅ Y) (eZ : Z' ≅ Z)
    (h : IsTensorHexagonAt d X' Y' Z') : IsTensorHexagonAt d X Y Z := by
  have : IsIso (d.tensor.map (show (X', Y') ⟶ (X, Y) from (eX.hom, eY.hom))) :=
    isIso_tensor_map (d := d) eX.hom eY.hom
  have := isIso_tensor_map (d := d)
    (d.tensor.map (show (X', Y') ⟶ (X, Y) from (eX.hom, eY.hom))) eZ.hom
  rw [IsTensorHexagonAt, ← cancel_epi (d.tensor.map (show
    (d.tensor.obj (X', Y'), Z') ⟶ (d.tensor.obj (X, Y), Z) from
    (d.tensor.map (show (X', Y') ⟶ (X, Y) from (eX.hom, eY.hom)), eZ.hom))),
    tensorHexagon_lhs_naturality, tensorHexagon_rhs_naturality, h]

end Abstract

section Transport

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
  {S : Type u₂} [CommRing S] [HasDerivedCategory.{w₂} (ModuleCat.{v₂} S)]
  (d : DerivedHomAdjunction R) (one : DerivedCategory (ModuleCat.{v₁} R))
  (lam : ∀ K : DerivedCategory (ModuleCat.{v₁} R), d.tensor.obj (one, K) ≅ K)
  (e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S))
  [e.functor.Additive]

/-- A left unitor for an adjunction transported along an additive equivalence of derived
categories: its tensor unit is the image of the original one, and the unitor is the original one
conjugated by the unit and counit of the equivalence. `DerivedHomAdjunction.transport` carries
no unitor of its own, and neither does `derivedHomAdjunctionOverRing`. -/
public def transportUnitorLeft (K : DerivedCategory (ModuleCat.{v₂} S)) :
    (d.transport e).tensor.obj (e.functor.obj one, K) ≅ K :=
  e.functor.mapIso (d.tensor.mapIso ((e.unitIso.app one).symm.prod
      (Iso.refl (e.inverse.obj K))) ≪≫ lam (e.inverse.obj K)) ≪≫ e.counitIso.app K

omit [e.functor.Additive] in
/-- Cancelling the unit of the equivalence against its counit. -/
private theorem map_comp_unit_counit {W Z : DerivedCategory (ModuleCat.{v₁} R)} (x : W ⟶ Z) :
    e.functor.map (x ≫ e.unit.app Z) ≫ e.counit.app (e.functor.obj Z) = e.functor.map x := by
  rw [e.functor.map_comp, Category.assoc, Equivalence.functor_unit_comp, Category.comp_id]

omit [e.functor.Additive] in
/-- The transported unitor pulled back through the inverse equivalence, in the unfolded form
that the transported structure presents. -/
private theorem inverse_map_unitor_aux (K : DerivedCategory (ModuleCat.{v₂} S)) :
    e.inverse.map (e.functor.map (d.tensor.map
          (show (e.inverse.obj (e.functor.obj one), e.inverse.obj K) ⟶
            (one, e.inverse.obj K) from
            (e.unitIso.inv.app one, 𝟙 (e.inverse.obj K))) ≫
          (lam (e.inverse.obj K)).hom) ≫ e.counitIso.hom.app K) =
      e.unitIso.inv.app (d.tensor.obj (e.inverse.obj (e.functor.obj one),
          e.inverse.obj K)) ≫
        d.tensor.map (show (e.inverse.obj (e.functor.obj one), e.inverse.obj K) ⟶
            (one, e.inverse.obj K) from
          (e.unitIso.inv.app one, 𝟙 (e.inverse.obj K))) ≫ (lam (e.inverse.obj K)).hom := by
  rw [e.inverse.map_comp, Equivalence.inv_fun_map]
  simp only [Category.assoc]
  rw [Equivalence.unit_inverse_comp, Category.comp_id]

/-- The inverse equivalence sends the transported unitor to the original one, conjugated by the
unit of the equivalence. -/
public theorem inverse_map_transportUnitorLeft (K : DerivedCategory (ModuleCat.{v₂} S)) :
    e.inverse.map (transportUnitorLeft d one lam e K).hom =
      e.unitIso.inv.app (d.tensor.obj (e.inverse.obj (e.functor.obj one),
          e.inverse.obj K)) ≫
        d.tensor.map (show (e.inverse.obj (e.functor.obj one), e.inverse.obj K) ⟶
            (one, e.inverse.obj K) from
          (e.unitIso.inv.app one, 𝟙 (e.inverse.obj K))) ≫ (lam (e.inverse.obj K)).hom := by
  dsimp only [transport, transportTensor, transportUnitorLeft, Functor.comp_obj,
    Functor.comp_map, Functor.prod_obj, Functor.prod_map, Functor.id_obj]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Iso.refl_hom]
  exact inverse_map_unitor_aux d one lam e K

/-- Naturality of the transported left unitor. -/
public theorem transportUnitorLeft_natural (hlam : IsUnitorNatural d one lam) :
    IsUnitorNatural (d.transport e) (e.functor.obj one) (transportUnitorLeft d one lam e) := by
  intro K K' f
  have hsp := d.tensor_map_eq_fst_comp_snd (B := one) (e.unitIso.inv.app one) (e.inverse.map f)
  dsimp only [transport, transportTensor, transportUnitorLeft, Functor.comp_obj,
    Functor.comp_map, Functor.prod_obj, Functor.prod_map, Functor.id_obj]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Iso.refl_hom]
  rw [CategoryTheory.Functor.map_id, ← Category.assoc, ← e.functor.map_comp,
    ← Category.assoc, d.tensor_map_comp]
  simp only [Category.id_comp, Category.comp_id]
  rw [hsp, Category.assoc, hlam (e.inverse.map f), ← Category.assoc, e.functor.map_comp,
    Category.assoc, Equivalence.counit_naturality]
  simp only [Category.assoc]

/-- The unitor triangle transports along an additive equivalence of derived categories. -/
public theorem isUnitorTriangleAt_transport (hlam : IsUnitorNatural d one lam)
    (htri : ∀ K X : DerivedCategory (ModuleCat.{v₁} R), IsUnitorTriangleAt d one lam K X)
    (K X : DerivedCategory (ModuleCat.{v₂} S)) :
    IsUnitorTriangleAt (d.transport e) (e.functor.obj one)
      (transportUnitorLeft d one lam e) K X := by
  have hsp := d.tensor_map_eq_fst_comp_snd (B := one)
    (C := d.tensor.obj (e.inverse.obj K, e.inverse.obj X)) (e.unitIso.inv.app one)
    (e.unitIso.hom.app (d.tensor.obj (e.inverse.obj K, e.inverse.obj X)))
  have hnatα : d.tensor.map (show (d.tensor.obj (e.inverse.obj (e.functor.obj one),
          e.inverse.obj K), e.inverse.obj X) ⟶
        (d.tensor.obj (one, e.inverse.obj K), e.inverse.obj X) from
        (d.tensor.map (show (e.inverse.obj (e.functor.obj one), e.inverse.obj K) ⟶
            (one, e.inverse.obj K) from
            (e.unitIso.inv.app one, 𝟙 (e.inverse.obj K))), 𝟙 (e.inverse.obj X))) ≫
      (d.tensorAssoc one (e.inverse.obj K) (e.inverse.obj X)).hom =
      (d.tensorAssoc (e.inverse.obj (e.functor.obj one)) (e.inverse.obj K)
          (e.inverse.obj X)).hom ≫
        d.tensor.map (show (e.inverse.obj (e.functor.obj one),
            d.tensor.obj (e.inverse.obj K, e.inverse.obj X)) ⟶
          (one, d.tensor.obj (e.inverse.obj K, e.inverse.obj X)) from
          (e.unitIso.inv.app one,
            𝟙 (d.tensor.obj (e.inverse.obj K, e.inverse.obj X)))) := by
    have h := d.tensorAssoc_naturality (e.unitIso.inv.app one) (𝟙 (e.inverse.obj K))
      (𝟙 (e.inverse.obj X))
    rw [d.tensor_map_id] at h
    exact h
  have hlam' : d.tensor.map (show (one, d.tensor.obj (e.inverse.obj K, e.inverse.obj X)) ⟶
        (one, e.inverse.obj (e.functor.obj
          (d.tensor.obj (e.inverse.obj K, e.inverse.obj X)))) from
        (𝟙 one,
          e.unitIso.hom.app (d.tensor.obj (e.inverse.obj K, e.inverse.obj X)))) ≫
      (lam (e.inverse.obj (e.functor.obj
        (d.tensor.obj (e.inverse.obj K, e.inverse.obj X))))).hom =
      (lam (d.tensor.obj (e.inverse.obj K, e.inverse.obj X))).hom ≫
        e.unitIso.hom.app (d.tensor.obj (e.inverse.obj K, e.inverse.obj X)) :=
    hlam _
  have htri' : (d.tensorAssoc one (e.inverse.obj K) (e.inverse.obj X)).hom ≫
      (lam (d.tensor.obj (e.inverse.obj K, e.inverse.obj X))).hom =
      d.tensor.map (show (d.tensor.obj (one, e.inverse.obj K), e.inverse.obj X) ⟶
        (e.inverse.obj K, e.inverse.obj X) from
        ((lam (e.inverse.obj K)).hom, 𝟙 (e.inverse.obj X))) :=
    htri (e.inverse.obj K) (e.inverse.obj X)
  rw [IsUnitorTriangleAt]
  dsimp only [transport, transportTensor, transportTensorAssoc, transportUnitorLeft,
    Functor.comp_obj, Functor.comp_map, Functor.prod_obj, Functor.prod_map, Functor.id_obj]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Iso.refl_hom]
  rw [CategoryTheory.Functor.map_id, inverse_map_unitor_aux d one lam e K,
    ← Category.assoc, ← e.functor.map_comp]
  simp only [Category.assoc]
  rw [d.tensor_map_comp_assoc]
  simp only [Category.id_comp, Category.comp_id, Functor.comp_obj, Functor.id_obj]
  rw [hsp]
  simp only [Category.assoc]
  rw [hlam', ← reassoc_of% hnatα, reassoc_of% htri', d.tensor_map_comp_assoc,
    d.tensor_map_comp_assoc]
  simp only [Category.comp_id, Category.assoc]
  rw [map_comp_unit_counit]

/-- The braiding hexagon transports along an additive equivalence of derived categories. -/
public theorem isTensorHexagonAt_transport
    (hhex : ∀ X Y Z : DerivedCategory (ModuleCat.{v₁} R), IsTensorHexagonAt d X Y Z)
    (X Y Z : DerivedCategory (ModuleCat.{v₂} S)) :
    IsTensorHexagonAt (d.transport e) X Y Z := by
  have hswapnat : d.tensor.map (show (e.inverse.obj X,
          d.tensor.obj (e.inverse.obj Y, e.inverse.obj Z)) ⟶
        (e.inverse.obj X, e.inverse.obj (e.functor.obj
          (d.tensor.obj (e.inverse.obj Y, e.inverse.obj Z)))) from
        (𝟙 (e.inverse.obj X),
          e.unitIso.hom.app (d.tensor.obj (e.inverse.obj Y, e.inverse.obj Z)))) ≫
      (d.tensorSwap (e.inverse.obj X) (e.inverse.obj (e.functor.obj
        (d.tensor.obj (e.inverse.obj Y, e.inverse.obj Z))))).hom =
      (d.tensorSwap (e.inverse.obj X)
          (d.tensor.obj (e.inverse.obj Y, e.inverse.obj Z))).hom ≫
        d.tensor.map (show (d.tensor.obj (e.inverse.obj Y, e.inverse.obj Z),
            e.inverse.obj X) ⟶
          (e.inverse.obj (e.functor.obj
            (d.tensor.obj (e.inverse.obj Y, e.inverse.obj Z))), e.inverse.obj X) from
          (e.unitIso.hom.app (d.tensor.obj (e.inverse.obj Y, e.inverse.obj Z)),
            𝟙 (e.inverse.obj X))) :=
    d.tensorSwap_naturality _ _
  have hc₁ := d.tensor_map_fst_comp_eq_id
    (e.unitIso.hom.app (d.tensor.obj (e.inverse.obj Y, e.inverse.obj Z)))
    (e.unitIso.inv.app (d.tensor.obj (e.inverse.obj Y, e.inverse.obj Z)))
    (e.unitIso.hom_inv_id_app _) (e.inverse.obj X)
  have hc₂ := d.tensor_map_fst_comp_eq_id
    (e.unitIso.hom.app (d.tensor.obj (e.inverse.obj Y, e.inverse.obj X)))
    (e.unitIso.inv.app (d.tensor.obj (e.inverse.obj Y, e.inverse.obj X)))
    (e.unitIso.hom_inv_id_app _) (e.inverse.obj Z)
  have hc₃ := d.tensor_map_snd_comp_eq_id (e.inverse.obj Y)
    (e.unitIso.hom.app (d.tensor.obj (e.inverse.obj X, e.inverse.obj Z)))
    (e.unitIso.inv.app (d.tensor.obj (e.inverse.obj X, e.inverse.obj Z)))
    (e.unitIso.hom_inv_id_app _)
  have hhex' : (d.tensorAssoc (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z)).hom ≫
      (d.tensorSwap (e.inverse.obj X)
        (d.tensor.obj (e.inverse.obj Y, e.inverse.obj Z))).hom ≫
      (d.tensorAssoc (e.inverse.obj Y) (e.inverse.obj Z) (e.inverse.obj X)).hom =
      d.tensor.map (show (d.tensor.obj (e.inverse.obj X, e.inverse.obj Y),
          e.inverse.obj Z) ⟶
          (d.tensor.obj (e.inverse.obj Y, e.inverse.obj X), e.inverse.obj Z) from
          ((d.tensorSwap (e.inverse.obj X) (e.inverse.obj Y)).hom, 𝟙 (e.inverse.obj Z))) ≫
        (d.tensorAssoc (e.inverse.obj Y) (e.inverse.obj X) (e.inverse.obj Z)).hom ≫
        d.tensor.map (show (e.inverse.obj Y,
            d.tensor.obj (e.inverse.obj X, e.inverse.obj Z)) ⟶
          (e.inverse.obj Y, d.tensor.obj (e.inverse.obj Z, e.inverse.obj X)) from
          (𝟙 (e.inverse.obj Y),
            (d.tensorSwap (e.inverse.obj X) (e.inverse.obj Z)).hom)) :=
    hhex (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z)
  rw [IsTensorHexagonAt]
  dsimp only [transport, transportTensor, transportTensorAssoc, Functor.comp_obj,
    Functor.comp_map, Functor.prod_obj, Functor.prod_map, Functor.id_obj]
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.prod_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Iso.refl_hom]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Equivalence.inv_fun_map, Equivalence.inv_fun_map, d.tensor_map_fst_comp,
    d.tensor_map_fst_comp, d.tensor_map_snd_comp, d.tensor_map_snd_comp]
  simp only [← e.functor.map_comp]
  refine congrArg e.functor.map ?_
  simp only [Category.assoc]
  rw [reassoc_of% hswapnat, reassoc_of% hc₁, reassoc_of% hc₂, reassoc_of% hc₃,
    reassoc_of% hhex']

end Transport

section TransportIso

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
  {S : Type u₂} [CommRing S] [HasDerivedCategory.{w₂} (ModuleCat.{v₂} S)]

/-- **An isomorphism of derived tensor--Hom adjunctions along an additive equivalence of derived
categories.** Two adjunctions, over possibly different rings and in possibly different module
universes, are identified by comparison isomorphisms of both bifunctors *together with* the
compatibility of their two Hom equivalences.

The third field is what makes this an isomorphism of adjunctions rather than of the underlying
pairs of bifunctors: it says that transposing a morphism in one adjunction and carrying the
result across the equivalence is the same as carrying the morphism across and transposing it
there. Without it only object-level statements cross the bridge; with it a statement about a
transpose, hence about any morphism defined by transposition, crosses as well. -/
public structure TransportIso (d : DerivedHomAdjunction R) (d' : DerivedHomAdjunction S)
    (e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S)) where
  /-- The comparison of the two derived tensor products, natural in both variables. -/
  tensorIso : e.functor.prod e.functor ⋙ d'.tensor ≅ d.tensor ⋙ e.functor
  /-- The comparison of the two derived internal Homs, natural in both variables. -/
  homIso : e.functor.op.prod e.functor ⋙ d'.hom ≅ d.hom ⋙ e.functor
  /-- The two Hom equivalences agree under the two comparisons. -/
  homEquiv_comparison (K L M : DerivedCategory (ModuleCat.{v₁} R))
      (a : K ⟶ d.hom.obj (Opposite.op L, M)) :
    d'.homEquiv (e.functor.obj K) (e.functor.obj L) (e.functor.obj M)
        (e.functor.map a ≫ (homIso.app (Opposite.op L, M)).inv) =
      (tensorIso.app (K, L)).hom ≫ e.functor.map (d.homEquiv K L M a)

/-- The compatibility of the two Hom equivalences of a `TransportIso`, read in the inverse
direction: a transpose computed on the source side and carried across the equivalence is the
transpose computed on the target side. -/
public theorem TransportIso.homEquiv_symm_comparison {d : DerivedHomAdjunction R}
    {d' : DerivedHomAdjunction S}
    {e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S)}
    (i : TransportIso d d' e) (K L M : DerivedCategory (ModuleCat.{v₁} R))
    (g : d.tensor.obj (K, L) ⟶ M) :
    (d'.homEquiv (e.functor.obj K) (e.functor.obj L) (e.functor.obj M)).symm
        ((i.tensorIso.app (K, L)).hom ≫ e.functor.map g) =
      e.functor.map ((d.homEquiv K L M).symm g) ≫
        (i.homIso.app (Opposite.op L, M)).inv := by
  rw [AddEquiv.symm_apply_eq, i.homEquiv_comparison, AddEquiv.apply_symm_apply]

/-- **Evaluation crosses an isomorphism of adjunctions.** The evaluation morphism of the target
adjunction at a pair of objects carried across the equivalence is the image of the evaluation
morphism of the source adjunction, read through the internal-Hom comparison in the first tensor
factor and then through the tensor comparison. Evaluation is the transpose of an identity, so
this is the compatibility of the two Hom equivalences together with naturality of the target Hom
equivalence in its source. -/
public theorem TransportIso.evaluation_comparison {d : DerivedHomAdjunction R}
    {d' : DerivedHomAdjunction S}
    {e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S)}
    (i : TransportIso d d' e) (L M : DerivedCategory (ModuleCat.{v₁} R)) :
    d'.evaluation (e.functor.obj L) (e.functor.obj M) =
      d'.tensor.map
          (X := (d'.hom.obj (Opposite.op (e.functor.obj L), e.functor.obj M), e.functor.obj L))
          (Y := (e.functor.obj (d.hom.obj (Opposite.op L, M)), e.functor.obj L))
          ((i.homIso.app (Opposite.op L, M)).hom, 𝟙 (e.functor.obj L)) ≫
        (i.tensorIso.app (d.hom.obj (Opposite.op L, M), L)).hom ≫
        e.functor.map (d.evaluation L M) := by
  have h := i.homEquiv_comparison (d.hom.obj (Opposite.op L, M)) L M
    (𝟙 (d.hom.obj (Opposite.op L, M)))
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have key := d'.homEquiv_naturality_left
      (K := d'.hom.obj (Opposite.op (e.functor.obj L), e.functor.obj M))
      (K' := e.functor.obj (d.hom.obj (Opposite.op L, M)))
      (L := e.functor.obj L) (M := e.functor.obj M)
      (i.homIso.app (Opposite.op L, M)).inv
      (𝟙 (d'.hom.obj (Opposite.op (e.functor.obj L), e.functor.obj M)))
  rw [Category.comp_id, h] at key
  rw [show d.homEquiv (d.hom.obj (Opposite.op L, M)) L M
      (𝟙 (d.hom.obj (Opposite.op L, M))) = d.evaluation L M from rfl,
    show d'.homEquiv (d'.hom.obj (Opposite.op (e.functor.obj L), e.functor.obj M))
        (e.functor.obj L) (e.functor.obj M)
        (𝟙 (d'.hom.obj (Opposite.op (e.functor.obj L), e.functor.obj M))) =
      d'.evaluation (e.functor.obj L) (e.functor.obj M) from rfl] at key
  rw [key, ← Category.assoc,
    d'.tensor_map_fst_comp_eq_id _ _ (i.homIso.app (Opposite.op L, M)).hom_inv_id
      (e.functor.obj L)]
  exact (Category.id_comp _).symm

variable (d : DerivedHomAdjunction R)
  (e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S))
  [e.functor.Additive]

/-- **The Hom equivalence of a transported adjunction is the original one, conjugated.** The
transpose of a morphism `a` of the source category, read through the internal-Hom comparison of
`DerivedHomAdjunction.transportHomIso`, is the transpose of `a` read through the tensor
comparison of `DerivedHomAdjunction.transportTensorIso`.

Both comparisons are the unit of the equivalence inserted in each variable, so the identity
reduces to the three naturality laws of the original Hom equivalence — naturality in the source,
dinaturality in the internal-Hom variable, and naturality in the target — followed by the
cancellation of the unit against the counit. -/
public theorem transportHomEquiv_map (K L M : DerivedCategory (ModuleCat.{v₁} R))
    (a : K ⟶ d.hom.obj (Opposite.op L, M)) :
    d.transportHomEquiv e (e.functor.obj K) (e.functor.obj L) (e.functor.obj M)
        (e.functor.map a ≫ e.functor.map (d.hom.map
          (X := (Opposite.op L, M))
          (Y := (Opposite.op (e.inverse.obj (e.functor.obj L)),
            e.inverse.obj (e.functor.obj M)))
          ((e.unitIso.inv.app L).op, e.unit.app M))) =
      e.functor.map (d.tensor.map
          (X := (e.inverse.obj (e.functor.obj K), e.inverse.obj (e.functor.obj L)))
          (Y := (K, L)) (e.unitInv.app K, e.unitInv.app L)) ≫
        e.functor.map (d.homEquiv K L M a) := by
  have hsplit : d.hom.map
        (X := (Opposite.op L, M))
        (Y := (Opposite.op (e.inverse.obj (e.functor.obj L)),
          e.inverse.obj (e.functor.obj M)))
        ((e.unitIso.inv.app L).op, e.unit.app M) =
      d.hom.map (X := (Opposite.op L, M))
          (Y := (Opposite.op L, e.inverse.obj (e.functor.obj M)))
          (𝟙 (Opposite.op L), e.unit.app M) ≫
        d.hom.map (X := (Opposite.op L, e.inverse.obj (e.functor.obj M)))
          (Y := (Opposite.op (e.inverse.obj (e.functor.obj L)),
            e.inverse.obj (e.functor.obj M)))
          ((e.unitIso.inv.app L).op, 𝟙 (e.inverse.obj (e.functor.obj M))) := by
    rw [← d.hom.map_comp]
    congr 1
    simp
  have hinner : e.inverse.map (e.functor.map a ≫ e.functor.map (d.hom.map
        (X := (Opposite.op L, M))
        (Y := (Opposite.op (e.inverse.obj (e.functor.obj L)),
          e.inverse.obj (e.functor.obj M)))
        ((e.unitIso.inv.app L).op, e.unit.app M))) ≫
      e.unitInv.app (d.hom.obj (Opposite.op (e.inverse.obj (e.functor.obj L)),
        e.inverse.obj (e.functor.obj M))) =
      e.unitInv.app K ≫ (a ≫ d.hom.map (X := (Opposite.op L, M))
          (Y := (Opposite.op L, e.inverse.obj (e.functor.obj M)))
          (𝟙 (Opposite.op L), e.unit.app M)) ≫
        d.hom.map (X := (Opposite.op L, e.inverse.obj (e.functor.obj M)))
          (Y := (Opposite.op (e.inverse.obj (e.functor.obj L)),
            e.inverse.obj (e.functor.obj M)))
          ((e.unitIso.inv.app L).op, 𝟙 (e.inverse.obj (e.functor.obj M))) := by
    rw [e.inverse.map_comp, Equivalence.inv_fun_map, Equivalence.inv_fun_map, hsplit]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    simp
  dsimp only [transportHomEquiv]
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply]
  simp only [Adjunction.homAddEquiv_symm_apply, Adjunction.homEquiv_counit,
    Equivalence.toAdjunction_counit, Equivalence.symm_functor, Equivalence.symm_inverse,
    Equivalence.symm_counit]
  rw [hinner, d.homEquiv_naturality_left, d.homEquiv_dinaturality,
    d.homEquiv_naturality_right, ← Category.assoc, d.tensor_map_comp]
  simp only [Category.comp_id, Category.id_comp, Functor.id_obj]
  rw [e.functor.map_comp, e.functor.map_comp, Category.assoc, Category.assoc,
    Equivalence.functor_unit_comp, Category.comp_id]

/-- **`DerivedHomAdjunction.transport` is an isomorphism of adjunctions.** The two comparison
isomorphisms `transportTensorIso` and `transportHomIso` that the transport already carries are
compatible with the two Hom equivalences, by `transportHomEquiv_map`. So no datum of the
original adjunction beyond the three structure fields is needed to compare transposes across the
transport, and in particular a morphism-level statement about the original adjunction transports
to the transported one. -/
public def transportIso : TransportIso d (d.transport e) e where
  tensorIso := d.transportTensorIso e
  homIso := d.transportHomIso e
  homEquiv_comparison K L M a := transportHomEquiv_map d e K L M a

end TransportIso

end DerivedHomAdjunction

section Models

open CochainComplex

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Every object of the derived category of `R`-modules is isomorphic to the localization of a
K-flat cochain complex: take any representative and apply the K-flat resolution of
[stacks 06Y4]. -/
public theorem exists_kFlat_representative (X : DerivedCategory (ModuleCat.{u} R)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      P.KFlat ∧ Nonempty (DerivedCategory.Q.obj P ≅ X) := by
  obtain ⟨P, f, hP, -, hf, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage X)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩

/-- The left unitor of the canonical model-level adjunction is natural. -/
public theorem derivedHomAdjunction_isUnitorNatural :
    DerivedHomAdjunction.IsUnitorNatural
      (derivedHomAdjunction (R := R)).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (Model.Complex R)))
      (derivedHomAdjunction (R := R)).tensorUnitLeft :=
  fun f => (derivedHomAdjunction (R := R)).tensorUnitLeft_naturality f

/-- The left-unitor/associator triangle on K-flat representatives: there it is the chain-level
triangle `leftUnitor_tensor_hom` of the monoidal category of cochain complexes, transported
through the K-flat tensor comparisons. -/
private theorem unitorTriangle_models (P X : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : P.KFlat) (hX : X.KFlat) :
    DerivedHomAdjunction.IsUnitorTriangleAt
      (derivedHomAdjunction (R := R)).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (Model.Complex R)))
      (derivedHomAdjunction (R := R)).tensorUnitLeft
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj X) := by
  set d := derivedHomAdjunction (R := R)
  have h1 : (𝟙_ (Model.Complex R)).KFlat := DerivedHomData.unit_kFlat (R := R)
  have hPX : (P ⊗ X).KFlat := CochainComplex.KFlat.tensor R P X hP hX
  have hcomp := derivedHomAdjunction_tensorAssoc_comparison
    (R := R) (𝟙_ (Model.Complex R)) P X h1 hP hX hPX
  have hsplit := d.tensor_map_fst_comp (d.tensorIso (𝟙_ (Model.Complex R)) P hP).hom
    (DerivedCategory.Q.map (λ_ P).hom) (DerivedCategory.Q.obj X)
  have hnat := d.tensorIso_naturality (λ_ P).hom (𝟙 X) hX hX
  rw [CategoryTheory.Functor.map_id] at hnat
  have hchain : DerivedCategory.Q.map (α_ (𝟙_ (Model.Complex R)) P X).hom ≫
      DerivedCategory.Q.map (λ_ (P ⊗ X)).hom =
      DerivedCategory.Q.map ((λ_ P).hom ⊗ₘ 𝟙 X) := by
    rw [← CategoryTheory.Functor.map_comp]
    congr 1
    rw [leftUnitor_tensor_hom, Iso.hom_inv_id_assoc, tensorHom_id]
  rw [DerivedHomAdjunction.IsUnitorTriangleAt,
    ← cancel_mono (d.tensorIso P X hX).hom, Category.assoc,
    ← d.tensorUnitLeft_naturality (d.tensorIso P X hX).hom,
    ← d.tensorUnitLeft_comparison (P ⊗ X) hPX, ← d.tensorUnitLeft_comparison P hP,
    reassoc_of% hcomp, hsplit, Category.assoc, hnat, hchain]

/-- The left-unitor/associator triangle for the canonical model-level derived tensor--Hom
adjunction, at arbitrary objects of `D(R)`: associating `(1 ⊗ K) ⊗ X` and then removing the
unit agrees with removing the unit in the left factor. This is the identity that the biduality
computations of Stacks 47 reduce to, and it is not a field of `DerivedHomAdjunction`. -/
public theorem derivedHomAdjunction_unitorTriangle
    (K X : DerivedCategory (ModuleCat.{u} R)) :
    DerivedHomAdjunction.IsUnitorTriangleAt
      (derivedHomAdjunction (R := R)).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (Model.Complex R)))
      (derivedHomAdjunction (R := R)).tensorUnitLeft K X := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_kFlat_representative K
  obtain ⟨Y, hY, ⟨eY⟩⟩ := exists_kFlat_representative X
  exact DerivedHomAdjunction.isUnitorTriangleAt_of_iso derivedHomAdjunction_isUnitorNatural
    eP eY (unitorTriangle_models P Y hP hY)

/-- The braiding hexagon on K-flat representatives: there it is the chain-level hexagon
`BraidedCategory.hexagon_forward` of the Koszul symmetric monoidal structure on cochain
complexes, transported through the K-flat tensor comparisons. -/
private theorem tensorHexagon_models (A B C : CochainComplex (ModuleCat.{u} R) ℤ)
    (hA : A.KFlat) (hB : B.KFlat) (hC : C.KFlat) :
    DerivedHomAdjunction.IsTensorHexagonAt
      (derivedHomAdjunction (R := R)).toDerivedHomAdjunction
      (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) := by
  set d := derivedHomAdjunction (R := R)
  have hBC : (B ⊗ C).KFlat := CochainComplex.KFlat.tensor R B C hB hC
  have hAC : (A ⊗ C).KFlat := CochainComplex.KFlat.tensor R A C hA hC
  have hCA : (C ⊗ A).KFlat := CochainComplex.KFlat.tensor R C A hC hA
  have hα₁ := derivedHomAdjunction_tensorAssoc_comparison (R := R) A B C hA hB hC hBC
  have hα₂ := derivedHomAdjunction_tensorAssoc_comparison (R := R) B C A hB hC hA hCA
  have hα₃ := derivedHomAdjunction_tensorAssoc_comparison (R := R) B A C hB hA hC hAC
  have hβ₁ : (d.tensorSwap (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj (B ⊗ C))).hom ≫ (d.tensorIso (B ⊗ C) A hA).hom =
      (d.tensorIso A (B ⊗ C) hBC).hom ≫
        DerivedCategory.Q.map (Model.complexSwap R A (B ⊗ C)).hom :=
    d.tensorSwap_comparison A (B ⊗ C) hA hBC
  have hβ₂ : (d.tensorSwap (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)).hom ≫
        (d.tensorIso B A hA).hom =
      (d.tensorIso A B hB).hom ≫ DerivedCategory.Q.map (Model.complexSwap R A B).hom :=
    d.tensorSwap_comparison A B hA hB
  have hβ₃ : (d.tensorSwap (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj C)).hom ≫
        (d.tensorIso C A hA).hom =
      (d.tensorIso A C hC).hom ≫ DerivedCategory.Q.map (Model.complexSwap R A C).hom :=
    d.tensorSwap_comparison A C hA hC
  have hn₁ := d.tensorIso_naturality (𝟙 B) (Model.complexSwap R A C).hom hAC hCA
  rw [CategoryTheory.Functor.map_id] at hn₁
  have hn₂ := d.tensorIso_naturality (Model.complexSwap R A B).hom (𝟙 C) hC hC
  rw [CategoryTheory.Functor.map_id] at hn₂
  have hsplit₁ := d.tensor_map_snd_comp (DerivedCategory.Q.obj B) (d.tensorIso A C hC).hom
    (DerivedCategory.Q.map (Model.complexSwap R A C).hom)
  have hsplit₂ := d.tensor_map_fst_comp (d.tensorIso A B hB).hom
    (DerivedCategory.Q.map (Model.complexSwap R A B).hom) (DerivedCategory.Q.obj C)
  have hchain : DerivedCategory.Q.map (α_ A B C).hom ≫
        DerivedCategory.Q.map (Model.complexSwap R A (B ⊗ C)).hom ≫
        DerivedCategory.Q.map (α_ B C A).hom =
      DerivedCategory.Q.map ((Model.complexSwap R A B).hom ⊗ₘ 𝟙 C) ≫
        DerivedCategory.Q.map (α_ B A C).hom ≫
        DerivedCategory.Q.map (𝟙 B ⊗ₘ (Model.complexSwap R A C).hom) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    let := CochainComplex.Koszul.koszulSymmetric R
    rw [tensorHom_id, id_tensorHom]
    exact BraidedCategory.hexagon_forward A B C
  have hi1 : IsIso (d.tensor.map (show (DerivedCategory.Q.obj B,
      d.tensor.obj (DerivedCategory.Q.obj C, DerivedCategory.Q.obj A)) ⟶
      (DerivedCategory.Q.obj B, DerivedCategory.Q.obj (C ⊗ A)) from
      (𝟙 (DerivedCategory.Q.obj B), (d.tensorIso C A hA).hom))) :=
    DerivedHomAdjunction.isIso_tensor_map _ _
  rw [DerivedHomAdjunction.IsTensorHexagonAt,
    ← cancel_mono (d.tensor.map (show (DerivedCategory.Q.obj B,
        d.tensor.obj (DerivedCategory.Q.obj C, DerivedCategory.Q.obj A)) ⟶
        (DerivedCategory.Q.obj B, DerivedCategory.Q.obj (C ⊗ A)) from
        (𝟙 (DerivedCategory.Q.obj B), (d.tensorIso C A hA).hom)) ≫
      (d.tensorIso B (C ⊗ A) hCA).hom)]
  simp only [Category.assoc]
  rw [hα₂, ← d.tensorSwap_naturality_assoc (𝟙 (DerivedCategory.Q.obj A))
      (d.tensorIso B C hC).hom, reassoc_of% hβ₁, reassoc_of% hα₁,
    d.tensor_map_comp_assoc, Category.comp_id, hβ₃, hsplit₁, Category.assoc, hn₁,
    reassoc_of% hα₃, d.tensor_map_comp_assoc, Category.comp_id, hβ₂, hsplit₂,
    Category.assoc, reassoc_of% hn₂, hchain]

/-- The braiding hexagon for the canonical model-level derived tensor--Hom adjunction, at
arbitrary objects of `D(R)`: the derived symmetry moves a factor past a tensor product in one
step exactly as it does in two. Like the unitor triangle this is not a field of
`DerivedHomAdjunction`. -/
public theorem derivedHomAdjunction_tensorHexagon
    (X Y Z : DerivedCategory (ModuleCat.{u} R)) :
    DerivedHomAdjunction.IsTensorHexagonAt
      (derivedHomAdjunction (R := R)).toDerivedHomAdjunction X Y Z := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := exists_kFlat_representative X
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_kFlat_representative Y
  obtain ⟨C, hC, ⟨eC⟩⟩ := exists_kFlat_representative Z
  exact DerivedHomAdjunction.isTensorHexagonAt_of_iso eA eB eC
    (tensorHexagon_models A B C hA hB hC)

end Models

section OverRing

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

/-- The tensor unit of `derivedHomAdjunctionOverRing`: the localized complex unit over the
lifted ring `ULift R`, carried to `D(R)` by the scalar equivalence. The transported adjunction
carries no unit of its own. -/
public def derivedTensorUnit : DerivedCategory (ModuleCat.{max u v} R) :=
  (derivedScalarEquivalence.{u, v, w} R).functor.obj
    (DerivedCategory.Q.obj (𝟙_ (Model.Complex (ULift.{v} R))))

/-- The left unitor of `derivedHomAdjunctionOverRing`, obtained by transporting the left unitor
of the lifted model-level adjunction along the scalar equivalence. This is the datum that
`DerivedHomData.tensorUnitLeft` supplies on the model side and that the transported adjunction
of [stacks 0A63] lacks. -/
public def derivedTensorUnitLeft (K : DerivedCategory (ModuleCat.{max u v} R)) :
    (derivedHomAdjunctionOverRing.{u, v, w} R).tensor.obj
      (derivedTensorUnit.{u, v, w} R, K) ≅ K :=
  DerivedHomAdjunction.transportUnitorLeft
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).toDerivedHomAdjunction
    (DerivedCategory.Q.obj (𝟙_ (Model.Complex (ULift.{v} R))))
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorUnitLeft
    (derivedScalarEquivalence.{u, v, w} R) K

/-- The left unitor of `derivedHomAdjunctionOverRing` is natural. -/
public theorem derivedTensorUnitLeft_natural :
    DerivedHomAdjunction.IsUnitorNatural (derivedHomAdjunctionOverRing.{u, v, w} R)
      (derivedTensorUnit.{u, v, w} R) (derivedTensorUnitLeft.{u, v, w} R) :=
  DerivedHomAdjunction.transportUnitorLeft_natural _ _ _ _
    (derivedHomAdjunction_isUnitorNatural (R := ULift.{v} R))

/-- **The left-unitor/associator triangle for `derivedHomAdjunctionOverRing`**, the adjunction
used by the tagged statement of [stacks 0A63], at arbitrary objects of `D(R)`. Together with
`homEquiv_naturality_left`, `homEquiv_dinaturality` and `tensorSwap_naturality` this is the
identity that the biduality computations of Stacks 47 reduce to. -/
public theorem derivedTensorUnitLeft_triangle
    (K X : DerivedCategory (ModuleCat.{max u v} R)) :
    DerivedHomAdjunction.IsUnitorTriangleAt (derivedHomAdjunctionOverRing.{u, v, w} R)
      (derivedTensorUnit.{u, v, w} R) (derivedTensorUnitLeft.{u, v, w} R) K X :=
  DerivedHomAdjunction.isUnitorTriangleAt_transport _ _ _ _
    (derivedHomAdjunction_isUnitorNatural (R := ULift.{v} R))
    (derivedHomAdjunction_unitorTriangle (R := ULift.{v} R)) K X

/-- **The braiding hexagon for `derivedHomAdjunctionOverRing`**, the adjunction used by the
tagged statement of [stacks 0A63], at arbitrary objects of `D(R)`: the derived symmetry moves a
factor past a tensor product in one step exactly as it does in two. -/
public theorem derivedHomAdjunctionOverRing_tensorHexagon
    (X Y Z : DerivedCategory (ModuleCat.{max u v} R)) :
    DerivedHomAdjunction.IsTensorHexagonAt (derivedHomAdjunctionOverRing.{u, v, w} R) X Y Z :=
  DerivedHomAdjunction.isTensorHexagonAt_transport _ _
    (derivedHomAdjunction_tensorHexagon (R := ULift.{v} R)) X Y Z

section TwoSpellings

/-- `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` restricts scalars from `R`
  to `ULift R`
exactly as `derivedScalarEquivalence` restricts them back. -/
public theorem scalarEquivalence_functor_eq :
    (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, v, w} R).functor =
      (derivedScalarEquivalence.{u, v, w} R).inverse := rfl

/-- `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` restricts scalars from
  `ULift R` to `R`
exactly as `derivedScalarEquivalence` does. -/
public theorem scalarEquivalence_inverse_eq :
    (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, v, w} R).inverse =
      (derivedScalarEquivalence.{u, v, w} R).functor := rfl

/-- **The two library spellings of derived internal Hom are the same functor.**
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom R` and `(derivedHomAdjunctionOverRing R).hom`
  are both
`(derivedHomAdjunction (ULift R)).hom` conjugated by restriction of scalars along
`ULift.ringEquiv`, written through opposite spellings of that equivalence. Since the
conjugation uses only the two functors of the equivalence, and those agree by
`scalarEquivalence_functor_eq` and `scalarEquivalence_inverse_eq`, the two constants coincide:
results proved about either spelling transfer to the other by rewriting. -/
public theorem derivedInternalHom_eq :
    Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, v, w} R =
      (derivedHomAdjunctionOverRing.{u, v, w} R).hom := rfl

end TwoSpellings

section ScalarBridge

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] in
/-- The internal-Hom bifunctor of the lifted model-level adjunction is the canonical
internal-Hom bifunctor `DerivedInternalHom.Model.hom` over the lifted ring. Both are the Hom
half of `derivedHomAdjunction` over `ULift.{v} R`, whose own universe `max u v` is also the
module universe, so the model API applies to it. Consequently `derivedHomULiftIso` is already
the comparison of `DerivedInternalHom.Model.hom (ULift.{v} R)` with
`(derivedHomAdjunctionOverRing R).hom`, hence by `derivedInternalHom_eq` with
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom R`. -/
public theorem derivedHomAdjunctionULift_hom_eq :
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).hom =
      DerivedInternalHom.Model.hom (ULift.{v} R) := rfl

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] in
/-- The tensor bifunctor of the lifted model-level adjunction is `DerivedInternalHom.Model.tensor`
over the lifted ring, so `derivedTensorULiftIso` is the comparison of that bifunctor with
`(derivedHomAdjunctionOverRing R).tensor`. -/
public theorem derivedHomAdjunctionULift_tensor_eq :
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensor =
      DerivedInternalHom.Model.tensor (ULift.{v} R) := rfl

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] in
/-- The Hom equivalence of the lifted model-level adjunction is
`DerivedInternalHom.Model.homEquiv` over the lifted ring. -/
public theorem derivedHomAdjunctionULift_homEquiv_eq
    (K L M : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homEquiv K L M =
      DerivedInternalHom.Model.homEquiv K L M := rfl

/-- **The scalar bridge: `derivedHomAdjunctionOverRing R` is the model-level adjunction over
`ULift.{v} R` transported along `derivedScalarEquivalence`, as an isomorphism of adjunctions.**

Its two comparison isomorphisms are `derivedTensorULiftIso` and `derivedHomULiftIso`, which are
isomorphisms of bifunctors and hence natural in both variables; by
`derivedHomAdjunctionULift_hom_eq` and `derivedHomAdjunctionULift_tensor_eq` their source sides
are `DerivedInternalHom.Model.hom` and `DerivedInternalHom.Model.tensor` over `ULift.{v} R`, and
by `derivedInternalHom_eq` their target sides are the two library spellings of derived internal
Hom in the independent module universe. Its third field, obtained from
`DerivedHomAdjunction.transportIso`, is the compatibility of the two Hom equivalences: that is
what the object-level comparisons alone do not give, and what lets a statement about a transpose
over `ULift.{v} R` be read as a statement about the Hom equivalence
`homInternalHomEquiv` of [stacks 0A63] over `R`. -/
public def derivedHomAdjunctionOverRingIso :
    DerivedHomAdjunction.TransportIso
      (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).toDerivedHomAdjunction
      (derivedHomAdjunctionOverRing.{u, v, w} R) (derivedScalarEquivalence.{u, v, w} R) :=
  DerivedHomAdjunction.transportIso _ _

/-- The tensor comparison of the scalar bridge is `derivedTensorULiftIso`. -/
public theorem derivedHomAdjunctionOverRingIso_tensorIso :
    (derivedHomAdjunctionOverRingIso.{u, v, w} R).tensorIso =
      derivedTensorULiftIso.{u, v, w} R := rfl

/-- The internal-Hom comparison of the scalar bridge is `derivedHomULiftIso`. -/
public theorem derivedHomAdjunctionOverRingIso_homIso :
    (derivedHomAdjunctionOverRingIso.{u, v, w} R).homIso =
      derivedHomULiftIso.{u, v, w} R := rfl

/-- **The scalar bridge at the level of transposition.** The Hom equivalence
`homInternalHomEquiv` of [stacks 0A63] over `R`, in a module universe independent of the ring's,
computes the transpose of a morphism carried across `derivedScalarEquivalence` exactly as
`DerivedInternalHom.Model.homEquiv` over `ULift.{v} R` computes it there. This is the form in
which a morphism-level statement about the model-level internal Hom over the lifted ring becomes
a statement about the derived Hom adjunction over `R` itself. -/
public theorem modelHomEquiv_homInternalHomEquiv
    (K L M : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (a : K ⟶ (DerivedInternalHom.Model.hom (ULift.{v} R)).obj (Opposite.op L, M)) :
    homInternalHomEquiv.{u, v, w}
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj K)
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj L)
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj M)
        ((derivedScalarEquivalence.{u, v, w} R).functor.map a ≫
          ((derivedHomULiftIso.{u, v, w} R).app (Opposite.op L, M)).inv) =
      ((derivedTensorULiftIso.{u, v, w} R).app (K, L)).hom ≫
        (derivedScalarEquivalence.{u, v, w} R).functor.map
          (DerivedInternalHom.Model.homEquiv K L M a) :=
  (derivedHomAdjunctionOverRingIso.{u, v, w} R).homEquiv_comparison K L M a

/-- **The scalar bridge at the level of transposition, in the inverse direction.** A morphism out
of a derived tensor product over `ULift.{v} R`, carried across `derivedScalarEquivalence`, has as
its transpose for `homInternalHomEquiv` the image of its transpose for
`DerivedInternalHom.Model.homEquiv`. -/
public theorem modelHomEquiv_symm_homInternalHomEquiv_symm
    (K L M : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (g : (DerivedInternalHom.Model.tensor (ULift.{v} R)).obj (K, L) ⟶ M) :
    (homInternalHomEquiv.{u, v, w}
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj K)
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj L)
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj M)).symm
        (((derivedTensorULiftIso.{u, v, w} R).app (K, L)).hom ≫
          (derivedScalarEquivalence.{u, v, w} R).functor.map g) =
      (derivedScalarEquivalence.{u, v, w} R).functor.map
          ((DerivedInternalHom.Model.homEquiv K L M).symm g) ≫
        ((derivedHomULiftIso.{u, v, w} R).app (Opposite.op L, M)).inv :=
  (derivedHomAdjunctionOverRingIso.{u, v, w} R).homEquiv_symm_comparison K L M g

end ScalarBridge

end OverRing

end StacksDraft.DerivedHom

end
