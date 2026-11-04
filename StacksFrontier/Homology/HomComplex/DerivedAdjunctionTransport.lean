module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunction

/-!
# Chain-level value of the transported tensor--Hom transpose

The tensor--Hom adjunction `derivedHomAdjunctionOverRing` on `D(R)` for an arbitrary admissible
module universe is obtained from the fixed-universe construction `derivedHomAdjunctionULift` by
conjugating all of its data along the restriction-of-scalars equivalence
`derivedScalarEquivalence`. Conjugation leaves the transpose `homEquiv` described only by
abstract adjunction yoga, so none of the chain-level information recorded by
`DerivedHomData.homEquiv_symm_map_eq` survives in a usable form.

This module transports that information. The general statement is
`DerivedHomAdjunction.transportHomEquiv_apply_functor_obj`: at objects coming from the source
category, the transported transpose is the image of the original transpose, conjugated by the
two bifunctor comparisons `transportTensorIso` and `transportHomIso`. Specializing to the
scalar equivalence and feeding in the K-flat/K-injective chain formula gives
`derivedHomAdjunctionOverRing_homEquiv_symm_apply`, which evaluates the transpose of
Stacks 0A63 on representatives: the transpose of `h : K ⊗ L ⟶ I` is the localization of the
chain map `Φ_{K,L}` of Stacks 0A62 followed by postcomposition with `h`.

## Main results

* `DerivedHomAdjunction.homEquiv_comp_hom_map`: combined naturality of a transpose in all three
  variables.
* `DerivedHomAdjunction.transportTensor_map`: the conjugated tensor on a pair of morphisms is
  `e.functor` of the original tensor on the pair of `e.inverse`-images -- `rfl`, but recorded
  because keyed matching does not cross the projections between the two sides.
* `DerivedHomAdjunction.transportHomEquiv_apply_functor_obj` and
  `DerivedHomAdjunction.transportHomEquiv_symm_apply_functor_obj`: the transported transpose at
  transported objects.
* `derivedHomAdjunctionOverRing_homEquiv_symm_apply`: the chain-level transpose of Stacks 0A63
  at a K-flat second argument and a K-injective target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor MonoidalCategory

namespace StacksDraft.DerivedHom

universe u v t w w' u₁ u₂ v₁ v₂ w₁ w₂

namespace DerivedHomAdjunction

section Naturality

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
  (d : DerivedHomAdjunction R)

/-- Naturality of the tensor--Hom transpose in all three variables at once: the three separate
naturality fields of `DerivedHomAdjunction`, composed. -/
theorem homEquiv_comp_hom_map {K K' L L' M M' : DerivedCategory (ModuleCat.{v₁} R)}
    (f : K' ⟶ K) (p : L' ⟶ L) (q : M ⟶ M') (a : K ⟶ d.hom.obj (Opposite.op L, M)) :
    d.homEquiv K' L' M' (f ≫ a ≫ d.hom.map
        (show (Opposite.op L, M) ⟶ (Opposite.op L', M') from (p.op, q))) =
      d.tensor.map (show (K', L') ⟶ (K, L) from (f, p)) ≫ d.homEquiv K L M a ≫ q := by
  have hsplit : (show (Opposite.op L, M) ⟶ (Opposite.op L', M') from (p.op, q)) =
      (show (Opposite.op L, M) ⟶ (Opposite.op L', M) from (p.op, 𝟙 M)) ≫
        (show (Opposite.op L', M) ⟶ (Opposite.op L', M') from (𝟙 (Opposite.op L'), q)) := by
    simp only [prod_comp, Category.comp_id, Category.id_comp]
  rw [hsplit, d.hom.map_comp, ← Category.assoc a, d.homEquiv_naturality_left,
    d.homEquiv_naturality_right, d.homEquiv_dinaturality, ← Category.assoc, ← Category.assoc,
    d.tensor_map_comp, Category.comp_id, Category.id_comp, Category.assoc]

end Naturality

section Transport

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
  {S : Type u₂} [CommRing S] [HasDerivedCategory.{w₂} (ModuleCat.{v₂} S)]
  (d : DerivedHomAdjunction R)
  (e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S))
  [e.functor.Additive]

/-- The functor of the inverse equivalence `e.symm` is additive: it is `e.inverse`, which is
additive as the inverse of the additive functor `e.functor`. -/
local instance : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive

/-- The inverse of the transported Hom comparison is the image of a single `hom`-functorial map
built from the unit of the equivalence. -/
theorem transportHomIso_app_inv (L M : DerivedCategory (ModuleCat.{v₁} R)) :
    ((d.transportHomIso e).app (Opposite.op L, M)).inv =
      e.functor.map (d.hom.map (show (Opposite.op L, M) ⟶
        (Opposite.op (e.inverse.obj (e.functor.obj L)), e.inverse.obj (e.functor.obj M)) from
        ((e.unitIso.inv.app L).op, e.unit.app M))) := rfl

/-- The transported tensor comparison is the image of a single `tensor`-functorial map built
from the unit of the equivalence. -/
theorem transportTensorIso_app_hom (K L : DerivedCategory (ModuleCat.{v₁} R)) :
    ((d.transportTensorIso e).app (K, L)).hom =
      e.functor.map (d.tensor.map (show (e.inverse.obj (e.functor.obj K),
        e.inverse.obj (e.functor.obj L)) ⟶ (K, L) from
        (e.unitIso.inv.app K, e.unitIso.inv.app L))) := rfl

omit [e.functor.Additive] in
/-- **The conjugated tensor on morphisms.**  `DerivedHomAdjunction.transportTensor` is the
reducible composite `e.inverse.prod e.inverse ⋙ d.tensor ⋙ e.functor`, so its action on a pair
of morphisms is `e.functor` of `d.tensor` of the pair of images under `e.inverse`.

This is the step that puts the left-hand side of a conjugated equation into the shape
`CategoryTheory.Equivalence.inverse_map_comp_unitIso_inv_eq_iff` consumes.  It holds by `rfl`,
but the equation is recorded because keyed matching does not cross the three `Functor.comp` and
`Functor.prod` projections that separate the two sides. -/
theorem transportTensor_map {K K' L L' : DerivedCategory (ModuleCat.{v₂} S)}
    (u : K ⟶ K') (p : L ⟶ L') :
    (d.transportTensor e).map (show (K, L) ⟶ (K', L') from (u, p)) =
      e.functor.map (d.tensor.map (show (e.inverse.obj K, e.inverse.obj L) ⟶
        (e.inverse.obj K', e.inverse.obj L') from (e.inverse.map u, e.inverse.map p))) := rfl

/-- The transported transpose, evaluated at objects coming from the source category: it is the
image under `e.functor` of the original transpose, conjugated by the two bifunctor comparisons
`transportHomIso` and `transportTensorIso`. -/
theorem transportHomEquiv_apply_functor_obj (K L M : DerivedCategory (ModuleCat.{v₁} R))
    (a : K ⟶ d.hom.obj (Opposite.op L, M)) :
    d.transportHomEquiv e (e.functor.obj K) (e.functor.obj L) (e.functor.obj M)
        (e.functor.map a ≫ ((d.transportHomIso e).app (Opposite.op L, M)).inv) =
      ((d.transportTensorIso e).app (K, L)).hom ≫ e.functor.map (d.homEquiv K L M a) := by
  have hA : (e.symm.toAdjunction.homEquiv (e.functor.obj K)
        (d.hom.obj (Opposite.op (e.inverse.obj (e.functor.obj L)),
          e.inverse.obj (e.functor.obj M)))).symm
        (e.functor.map a ≫ ((d.transportHomIso e).app (Opposite.op L, M)).inv) =
      e.unitIso.inv.app K ≫ a ≫ d.hom.map (show (Opposite.op L, M) ⟶
        (Opposite.op (e.inverse.obj (e.functor.obj L)), e.inverse.obj (e.functor.obj M)) from
        ((e.unitIso.inv.app L).op, e.unit.app M)) := by
    rw [d.transportHomIso_app_inv e, ← e.functor.map_comp, Adjunction.homEquiv_counit]
    exact e.unitIso.inv.naturality _
  have hB := d.homEquiv_comp_hom_map (K := K) (L := L) (M := M)
    (K' := e.inverse.obj (e.functor.obj K))
    (L' := e.inverse.obj (e.functor.obj L)) (M' := e.inverse.obj (e.functor.obj M))
    (e.unitIso.inv.app K) (e.unitIso.inv.app L) (e.unit.app M) a
  have hC : (e.toAdjunction.homEquiv (d.tensor.obj (e.inverse.obj (e.functor.obj K),
        e.inverse.obj (e.functor.obj L))) (e.functor.obj M)).symm
        (d.tensor.map (show (e.inverse.obj (e.functor.obj K),
            e.inverse.obj (e.functor.obj L)) ⟶ (K, L) from
          (e.unitIso.inv.app K, e.unitIso.inv.app L)) ≫ d.homEquiv K L M a ≫ e.unit.app M) =
      e.functor.map (d.tensor.map (show (e.inverse.obj (e.functor.obj K),
          e.inverse.obj (e.functor.obj L)) ⟶ (K, L) from
        (e.unitIso.inv.app K, e.unitIso.inv.app L))) ≫
        e.functor.map (d.homEquiv K L M a) := by
    rw [Adjunction.homEquiv_counit]
    simp only [Equivalence.toAdjunction_counit, e.functor.map_comp, Category.assoc,
      Equivalence.functor_unit_comp, Category.comp_id]
  have key : d.transportHomEquiv e (e.functor.obj K) (e.functor.obj L) (e.functor.obj M)
        (e.functor.map a ≫ ((d.transportHomIso e).app (Opposite.op L, M)).inv) =
      e.functor.map (d.tensor.map (show (e.inverse.obj (e.functor.obj K),
          e.inverse.obj (e.functor.obj L)) ⟶ (K, L) from
        (e.unitIso.inv.app K, e.unitIso.inv.app L))) ≫
        e.functor.map (d.homEquiv K L M a) := by
    simp only [transportHomEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_symm_apply]
    rw [hA, hB, hC]
  exact key

/-- The inverse direction of `transportHomEquiv_apply_functor_obj`. -/
theorem transportHomEquiv_symm_apply_functor_obj (K L M : DerivedCategory (ModuleCat.{v₁} R))
    (g : d.tensor.obj (K, L) ⟶ M) :
    (d.transportHomEquiv e (e.functor.obj K) (e.functor.obj L) (e.functor.obj M)).symm
        (((d.transportTensorIso e).app (K, L)).hom ≫ e.functor.map g) =
      e.functor.map ((d.homEquiv K L M).symm g) ≫
        ((d.transportHomIso e).app (Opposite.op L, M)).inv := by
  have h := d.transportHomEquiv_apply_functor_obj e K L M ((d.homEquiv K L M).symm g)
  rw [AddEquiv.apply_symm_apply] at h
  exact (AddEquiv.symm_apply_eq _).mpr h.symm

end Transport

end DerivedHomAdjunction

attribute [local instance] HasDerivedCategory.standard

open CochainComplex HomComplex in
/-- **Chain-level transpose for Stacks 0A63.** The additive equivalence
`(derivedHomAdjunctionOverRing R).homEquiv` of Stacks 0A63 is opaque at a general object. At a
K-flat second argument `L` and a K-injective target `I`, transported to `D(R)` along
`derivedScalarEquivalence`, its inverse is computed on representatives by the chain map
`Φ_{K,L}` of Stacks 0A62 followed by postcomposition with `h`, read through the two model
isomorphisms `derivedTensorModelIso` and `derivedHomModelIso`. -/
theorem derivedHomAdjunctionOverRing_homEquiv_symm_apply {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K L I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (hL : L.KFlat)
    [I.IsKInjective] (h : K ⊗ L ⟶ I) :
    ((derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I))).symm
        ((derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
          (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h)) =
      (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map
          (Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} R) K L ≫
            Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} R) L (K ⊗ L) I h)) ≫
        (derivedHomModelIso.{u, v, w} R L I).inv := by
  have harg : (derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
        (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h) =
      ((derivedTensorULiftIso.{u, v, w} R).app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)).hom ≫
        (derivedScalarEquivalence.{u, v, w} R).functor.map
          (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
            DerivedCategory.Q.map h) := by
    refine (Category.assoc _ _ _).trans ?_
    rw [Functor.mapIso_hom, ← (derivedScalarEquivalence.{u, v, w} R).functor.map_comp]
  have hchain : ((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homEquiv
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)).symm
        (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
          DerivedCategory.Q.map h) =
      DerivedCategory.Q.map
          (Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} R) K L ≫
            Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} R) L (K ⊗ L) I h) ≫
        ((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homIso L I).inv :=
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homEquiv_symm_map_eq K L I hL h
  rw [harg]
  refine Eq.trans ((derivedHomAdjunctionULift.{u, v, max u v + 1}
      (R := R)).toDerivedHomAdjunction.transportHomEquiv_symm_apply_functor_obj
      (derivedScalarEquivalence.{u, v, w} R) (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)
      (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
        DerivedCategory.Q.map h)) ?_
  rw [hchain, (derivedScalarEquivalence.{u, v, w} R).functor.map_comp]
  exact Category.assoc _ _ _

open CochainComplex HomComplex in
/-- **Chain-level transpose for Stacks 0A63, forward direction.** The forward reading of
`derivedHomAdjunctionOverRing_homEquiv_symm_apply`: the transpose of the localized chain map
`Φ_{K,L}` of Stacks 0A62 followed by postcomposition with `h`, read into derived Hom through
`derivedHomModelIso`, is `h` itself read through `derivedTensorModelIso`. -/
theorem derivedHomAdjunctionOverRing_homEquiv_apply {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K L I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (hL : L.KFlat)
    [I.IsKInjective] (h : K ⊗ L ⟶ I) :
    (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I))
        ((derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map
            (Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} R) K L ≫
              Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} R) L (K ⊗ L) I h)) ≫
          (derivedHomModelIso.{u, v, w} R L I).inv) =
      (derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
        (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h) :=
  ((AddEquiv.symm_apply_eq _).mp
    (derivedHomAdjunctionOverRing_homEquiv_symm_apply.{u, v, w} K L I hL h)).symm

end StacksDraft.DerivedHom
