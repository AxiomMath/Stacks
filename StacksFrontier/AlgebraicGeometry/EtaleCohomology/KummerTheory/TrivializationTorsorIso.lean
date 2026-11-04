module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TrivializationTorsor

/-!
# Isomorphic pairs have isomorphic torsors of trivializations

Let `(C, O)` be a ringed site, let `(L, α)` and `(M, β)` be pairs on it — invertible modules with
trivializations of their `n`-th tensor powers — and let `e : L ≅ M` be an isomorphism carrying one
trivialization to the other, that is, an isomorphism of pairs. Then `e` carries the
trivializations of `(L, α)` to the trivializations of `(M, β)`: it carries local generators to
local generators, and the trivialization value is unchanged because the `n`-th tensor power of `e`
intertwines the two trivializations. The resulting isomorphism of sheaves of sets is equivariant
for the sheaf of `n`-th roots of unity, since `e` is a morphism of modules and the action is
scaling. So the two torsors of trivializations are isomorphic and their first cohomology classes
agree.

This is part (2) of the proof of Tag 040Q — isomorphic pairs give rise to the same cohomology
class — for the second construction of the tag.

## Main definitions

* `Stacks.Cohomology.Torsors.Generators.normalizedMapOfIso` and `normalizedInvMapOfIso`: the two
  maps on trivializations induced by an isomorphism of pairs and by its inverse.
* `Stacks.Cohomology.Torsors.Generators.normalizedIsoOfIso`: the induced isomorphism of the two
  sheaves of trivializations.
* `AlgebraicGeometry.trivializationTorsorHomOfIso`: it read as a morphism of torsors.

## Main results

* `Stacks.Cohomology.Torsors.Generators.trivValue_map` and `trivValue_inv_map`: an isomorphism of
  pairs leaves the trivialization value unchanged, in both directions.
* `AlgebraicGeometry.trivializationTorsor_isIsomorphic_of_iso'`: **isomorphic pairs have
  equivariantly isomorphic torsors of trivializations.**
* `AlgebraicGeometry.trivializationTorsor_class_eq_of_iso'`: **hence the same isomorphism class of
  torsors**, and so the same first cohomology class.

## Implementation notes

The inverse map is written out separately rather than obtained as `normalizedMapOfIso` at
`e.symm`: that would need the `n`-th tensor power of `e.symm` to be the inverse of the `n`-th
tensor power of `e`, which is a further induction, whereas the compatibility hypothesis read
backwards gives the inverse directly through
`Stacks.Cohomology.Torsors.Generators.sheafIso_inv_app_hom_app` at `e` and at `e.symm`.

Equivariance is checked on underlying sections: the action is scaling by
`AlgebraicGeometry.rootUnit` on both sides and `e` is a morphism of modules, so it is one
application of `map_smul`.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 040P](https://stacks.math.columbia.edu/tag/040P)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.Torsors (AbelianTorsor torsorSetoid)
open Stacks.Cohomology.Torsors.Generators
open Stacks.SheafOfModules (IsInvertible)

universe t w v u

namespace Stacks.Cohomology.Torsors.Generators

section Site

variable (X : RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (e : L ≅ M)

/-- **An isomorphism of pairs leaves the trivialization value unchanged.** -/
theorem trivValue_map (hcompat : powerMap X e n ≪≫ bl = al) (U : X.C)
    (s : L.val.obj (op U)) :
    trivValue X M n bl U ((e.hom.val.app (op U)).hom s) = trivValue X L n al U s := by
  subst hcompat
  exact (congrArg (fun z => unitVal X U ((bl.hom.val.app (op U)).hom z))
    (powerSection_map X e U s n).symm).trans
      (congrArg (unitVal X U) (comp_val_app_apply X (powerMap X e n).hom bl.hom (op U) _))

/-- **The inverse of an isomorphism of pairs leaves the trivialization value unchanged.** -/
theorem trivValue_inv_map (hcompat : powerMap X e n ≪≫ bl = al) (U : X.C)
    (t : M.val.obj (op U)) :
    trivValue X L n al U ((e.inv.val.app (op U)).hom t) = trivValue X M n bl U t := by
  refine Eq.trans (trivValue_map X L M n al bl e hcompat U
    ((e.inv.val.app (op U)).hom t)).symm ?_
  exact congrArg (fun z => trivValue X M n bl U z)
    (sheafIso_inv_app_hom_app X e.symm (op U) t)

/-- The map on trivializations induced by an isomorphism of pairs. -/
def normalizedMapOfIso (hcompat : powerMap X e n ≪≫ bl = al) :
    (normalizedSheaf X L n al).obj ⟶ (normalizedSheaf X M n bl).obj where
  app U := ↾(fun s : (normalizedSubfunctor X L n al).obj U =>
    (⟨(e.hom.val.app (op U.unop)).hom s.val,
      (generatorSections_mapIso' X e U.unop ⟨s.val, s.property.1⟩).property,
      (trivValue_map X L M n al bl e hcompat U.unop s.val).trans s.property.2⟩ :
        (normalizedSubfunctor X M n bl).obj U))
  naturality _ _ f := ConcreteCategory.hom_ext _ _ fun s =>
    Subtype.ext (PresheafOfModules.naturality_apply e.hom.val f s.val)

/-- The map on trivializations induced by the inverse of an isomorphism of pairs. -/
def normalizedInvMapOfIso (hcompat : powerMap X e n ≪≫ bl = al) :
    (normalizedSheaf X M n bl).obj ⟶ (normalizedSheaf X L n al).obj where
  app U := ↾(fun t : (normalizedSubfunctor X M n bl).obj U =>
    (⟨(e.inv.val.app (op U.unop)).hom t.val,
      (generatorSections_mapIso' X e.symm U.unop ⟨t.val, t.property.1⟩).property,
      (trivValue_inv_map X L M n al bl e hcompat U.unop t.val).trans t.property.2⟩ :
        (normalizedSubfunctor X L n al).obj U))
  naturality _ _ f := ConcreteCategory.hom_ext _ _ fun t =>
    Subtype.ext (PresheafOfModules.naturality_apply e.inv.val f t.val)

/-- **The isomorphism of the two sheaves of trivializations** induced by an isomorphism of
pairs. -/
def normalizedIsoOfIso (hcompat : powerMap X e n ≪≫ bl = al) :
    (normalizedSheaf X L n al).obj ≅ (normalizedSheaf X M n bl).obj where
  hom := normalizedMapOfIso X L M n al bl e hcompat
  inv := normalizedInvMapOfIso X L M n al bl e hcompat
  hom_inv_id := NatTrans.ext <| funext fun U => ConcreteCategory.hom_ext _ _ fun s =>
    Subtype.ext (sheafIso_inv_app_hom_app X e (op U.unop) s.val)
  inv_hom_id := NatTrans.ext <| funext fun U => ConcreteCategory.hom_ext _ _ fun t =>
    Subtype.ext (sheafIso_inv_app_hom_app X e.symm (op U.unop) t.val)

/-- The underlying section of the image of a trivialization. -/
theorem normalizedMapOfIso_val (hcompat : powerMap X e n ≪≫ bl = al) (U : X.Cᵒᵖ)
    (s : (normalizedSubfunctor X L n al).obj U) :
    ((normalizedMapOfIso X L M n al bl e hcompat).app U s).val =
      (e.hom.val.app (op U.unop)).hom s.val := rfl

end Site

end Stacks.Cohomology.Torsors.Generators

namespace AlgebraicGeometry

section

variable {C : Type v} [Category.{u} C] (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (hO : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ))
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)
    [(schemeFunctionsRingedSite J F hO).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (schemeFunctionsRingedSite J F hO).J AddCommGrpCat.{u}]
    (hX : RingedSite.IsLocallyRinged (schemeFunctionsRingedSite J F hO))
    (hroot : LocalRoots (schemeFunctionsRingedSite J F hO) n)
    (L M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
    (hL : IsInvertible (schemeFunctionsRingedSite J F hO).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O).2 L)
    (hM : IsInvertible (schemeFunctionsRingedSite J F hO).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O).2 M)
    (al : tpow (schemeFunctionsRingedSite J F hO) L n ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
    (bl : tpow (schemeFunctionsRingedSite J F hO) M n ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))

/-- The isomorphism of pairs read as a morphism of the two torsors of trivializations. -/
def trivializationTorsorHomOfIso (e : L ≅ M)
    (hcompat : powerMap (schemeFunctionsRingedSite J F hO) e n ≪≫ bl = al) :
    (trivializationTorsor J F hO h n hX hroot L hL al).1.Hom
      (trivializationTorsor J F hO h n hX hroot M hM bl).1 where
  hom := (normalizedIsoOfIso (schemeFunctionsRingedSite J F hO) L M n al bl e hcompat).hom
  map_act U _ s := Subtype.ext <|
    (congrArg (e.hom.val.app (op U.unop)).hom (rootAct_val J F hO h n L al U _ s)).trans
      ((e.hom.val.app (op U.unop)).hom.map_smul _ s.val)

/-- **Isomorphic pairs have equivariantly isomorphic torsors of trivializations.** -/
theorem trivializationTorsor_isIsomorphic_of_iso'
    (e : L ≅ M)
    (hcompat : powerMap (schemeFunctionsRingedSite J F hO) e n ≪≫ bl = al) :
    AbelianTorsor.IsIsomorphic (trivializationTorsor J F hO h n hX hroot L hL al)
      (trivializationTorsor J F hO h n hX hroot M hM bl) :=
  ⟨trivializationTorsorHomOfIso J F hO h n hX hroot L M hL hM al bl e hcompat,
    inferInstanceAs (IsIso
      (normalizedIsoOfIso (schemeFunctionsRingedSite J F hO) L M n al bl e hcompat).hom)⟩

/-- **Isomorphic pairs have the same isomorphism class of torsors of trivializations**, hence the
same first cohomology class. This is part (2) of the proof of Tag 040Q. -/
theorem trivializationTorsor_class_eq_of_iso'
    (e : L ≅ M)
    (hcompat : powerMap (schemeFunctionsRingedSite J F hO) e n ≪≫ bl = al) :
    Quotient.mk (torsorSetoid (rootsOfUnitySheaf J F h n))
        (trivializationTorsor J F hO h n hX hroot L hL al) =
      Quotient.mk (torsorSetoid (rootsOfUnitySheaf J F h n))
        (trivializationTorsor J F hO h n hX hroot M hM bl) :=
  Quotient.sound
    (trivializationTorsor_isIsomorphic_of_iso' J F hO h n hX hroot L M hL hM al bl e hcompat)

end

end AlgebraicGeometry

end
