module

public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Transporting stalks and the function field along an isomorphism of schemes

An isomorphism `φ : V ≅ W` of schemes identifies the local ring of `V` at a point `z` with the
local ring of `W` at `φ z`, and — when the two schemes are irreducible — the function field of
`V` with the function field of `W`, because an isomorphism is in particular an open immersion and
therefore carries the generic point to the generic point.

This file constructs those two identifications and shows that they are compatible: the square
```
  O_{V,z}  ----->  R(V)
     |               |
     v               v
  O_{W,φz} ----->  R(W)
```
commutes, where the horizontal maps are the canonical ones from a local ring into the function
field (`AlgebraicGeometry.Scheme.stalkFunctionFieldAlgebra`, that is, specialization from the
generic point) and the vertical maps are the transports along `φ`. Everything is assembled out of
Mathlib's `AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap`, so no transport along the
equality of generic points is needed: that equality is absorbed into a
`TopCat.Presheaf.stalkCongr`.

## Main definitions

* `Stacks.Chow.stalkIsoOfIso` — the isomorphism `O_{V,z} ≅ O_{W,φz}` of local rings, and
  `Stacks.Chow.stalkRingEquivOfIso` the same as a `RingEquiv`.
* `Stacks.Chow.functionFieldIsoOfIso` — the isomorphism `R(V) ≅ R(W)` of function fields, and
  `Stacks.Chow.functionFieldRingEquivOfIso` the same as a `RingEquiv`.

## Main results

* `Stacks.Chow.genericPoint_map_of_iso` — an isomorphism carries the generic point to the
  generic point.
* `Stacks.Chow.functionFieldRingEquivOfIso_algebraMap` — the compatibility square above.

## References

* [Stacks Project, Tag 01RU](https://stacks.math.columbia.edu/tag/01RU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {V W : Scheme.{u}}

/-! ### Germs in the function field -/

/-- The canonical map from the local ring at a point of an irreducible scheme into the function
field is specialization from the generic point. -/
theorem algebraMap_stalk_functionField (X : Scheme.{u}) [IrreducibleSpace X] (x : X)
    (a : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk x) X.functionField a =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) a :=
  rfl

/-- The forward map of `TopCat.Presheaf.stalkCongr` is specialization, for any proof of the
specialization: `Specializes` is a proposition, so the two agree on the nose. -/
private theorem stalkCongr_hom_eq_stalkSpecializes {T : TopCat}
    (F : TopCat.Presheaf CommRingCat T) {x y : T} (e : Inseparable x y) (hs : y ⤳ x) :
    (F.stalkCongr e).hom = F.stalkSpecializes hs :=
  rfl

/-! ### The generic point -/

/-! ### Stalks -/

/-- The isomorphism of local rings `O_{V,z} ≅ O_{W,φz}` induced by an isomorphism of schemes
`φ : V ≅ W`: the inverse of the stalk map of `φ`, which is an isomorphism because `φ` is. -/
def stalkIsoOfIso (φ : V ≅ W) (z : V) :
    V.presheaf.stalk z ≅ W.presheaf.stalk (φ.hom.base z) :=
  (asIso (φ.hom.stalkMap z)).symm

/-- `Stacks.Chow.stalkIsoOfIso` as a ring isomorphism. -/
def stalkRingEquivOfIso (φ : V ≅ W) (z : V) :
    V.presheaf.stalk z ≃+* W.presheaf.stalk (φ.hom.base z) :=
  (stalkIsoOfIso φ z).commRingCatIsoToRingEquiv

/-- `Stacks.Chow.stalkRingEquivOfIso φ z` acts on a germ as the forward map of
`Stacks.Chow.stalkIsoOfIso φ z`. -/
@[simp]
theorem stalkRingEquivOfIso_apply (φ : V ≅ W) (z : V) (a : V.presheaf.stalk z) :
    stalkRingEquivOfIso φ z a = (stalkIsoOfIso φ z).hom a :=
  rfl

/-- The stalk map of `φ` at `z` is a left inverse of `Stacks.Chow.stalkIsoOfIso`. -/
@[simp]
theorem stalkIsoOfIso_hom_stalkMap_apply (φ : V ≅ W) (z : V)
    (b : W.presheaf.stalk (φ.hom.base z)) :
    (stalkIsoOfIso φ z).hom (φ.hom.stalkMap z b) = b := by
  rw [← CommRingCat.comp_apply]
  simp [stalkIsoOfIso]

/-- The stalk map of `φ` at `z` is a right inverse of `Stacks.Chow.stalkIsoOfIso`. -/
@[simp]
theorem stalkMap_stalkIsoOfIso_hom_apply (φ : V ≅ W) (z : V) (a : V.presheaf.stalk z) :
    φ.hom.stalkMap z ((stalkIsoOfIso φ z).hom a) = a := by
  rw [← CommRingCat.comp_apply]
  simp [stalkIsoOfIso]

/-! ### The function field -/

/-- The isomorphism of function fields `R(V) ≅ R(W)` induced by an isomorphism `φ : V ≅ W` of
irreducible schemes: the stalk isomorphism at the generic point of `V`, followed by the
identification of the stalk at `φ(η_V)` with the stalk at `η_W`. -/
def functionFieldIsoOfIso (φ : V ≅ W) [IrreducibleSpace V] [IrreducibleSpace W] :
    V.functionField ≅ W.functionField :=
  stalkIsoOfIso φ (genericPoint V) ≪≫
    W.presheaf.stalkCongr (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion φ.hom))

/-- `Stacks.Chow.functionFieldIsoOfIso` as a ring isomorphism. -/
def functionFieldRingEquivOfIso (φ : V ≅ W) [IrreducibleSpace V] [IrreducibleSpace W] :
    V.functionField ≃+* W.functionField :=
  (functionFieldIsoOfIso φ).commRingCatIsoToRingEquiv

/-- `Stacks.Chow.functionFieldRingEquivOfIso φ` acts on a rational function as the forward map of
`Stacks.Chow.functionFieldIsoOfIso φ`. -/
@[simp]
theorem functionFieldRingEquivOfIso_apply (φ : V ≅ W) [IrreducibleSpace V] [IrreducibleSpace W]
    (f : V.functionField) :
    functionFieldRingEquivOfIso φ f = (functionFieldIsoOfIso φ).hom f :=
  rfl

/-- **The compatibility square.** Sending a germ at `z` into the function field of `V` and then
across `φ` is the same as transporting it to a germ at `φ z` and then sending that into the
function field of `W`. -/
theorem functionFieldRingEquivOfIso_algebraMap (φ : V ≅ W) [IrreducibleSpace V]
    [IrreducibleSpace W] (z : V) (a : V.presheaf.stalk z) :
    functionFieldRingEquivOfIso φ (algebraMap (V.presheaf.stalk z) V.functionField a) =
      algebraMap (W.presheaf.stalk (φ.hom.base z)) W.functionField
        (stalkRingEquivOfIso φ z a) := by
  have hz : genericPoint V ⤳ z := (genericPoint_spec V).specializes trivial
  set b : W.presheaf.stalk (φ.hom.base z) := (stalkIsoOfIso φ z).hom a with hb
  have ha : a = φ.hom.stalkMap z b := by rw [hb, stalkMap_stalkIsoOfIso_hom_apply]
  rw [functionFieldRingEquivOfIso_apply, stalkRingEquivOfIso_apply, ← hb,
    algebraMap_stalk_functionField, algebraMap_stalk_functionField, ha,
    ← Scheme.Hom.stalkSpecializes_stalkMap_apply φ.hom (genericPoint V) z hz b,
    functionFieldIsoOfIso]
  have hgen : genericPoint W ⤳ φ.hom.base (genericPoint V) :=
    (genericPoint_spec W).specializes trivial
  rw [Iso.trans_hom, CommRingCat.comp_apply, stalkIsoOfIso_hom_stalkMap_apply,
    stalkCongr_hom_eq_stalkSpecializes W.presheaf _ hgen,
    TopCat.Presheaf.stalkSpecializes_comp_apply]

end Stacks.Chow

end
