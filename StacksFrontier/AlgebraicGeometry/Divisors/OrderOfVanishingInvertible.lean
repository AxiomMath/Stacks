module

public import StacksFrontier.AlgebraicGeometry.Divisors.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# The order of vanishing of a meromorphic section of an invertible module

Let `X` be a locally Noetherian integral scheme and let `L` be an *invertible* sheaf of
`𝒪_X`-modules. `StacksFrontier/AlgebraicGeometry/Divisors/OrderOfVanishing.lean` defines the
order of vanishing along a point `ξ` of codimension one from a generator of the stalk `L_ξ`
whose image at the generic point is a nonzero generator of `L_η`. This file supplies that
generator from invertibility alone, which is what Tag 02SF assumes: the trivializing section of
Tag 0B8M near `ξ` has exactly the bijectivity property that
`AlgebraicGeometry.nonempty_orderOfVanishingData_of_bijective_smul` consumes.

It also records the two bridges that let the result be read at the vocabulary of Tag 02SF: a
point of a scheme has coheight one exactly when the closure of its singleton has codimension one
(which is the defining condition on the generic point of a prime divisor), and an invertible
module is quasi-coherent.

## Main results

* `AlgebraicGeometry.coheight_eq_codimension_closureSingleton`: for a point of a scheme the
  coheight in the specialization order is the codimension of the closure of its singleton.
* `AlgebraicGeometry.nonempty_orderOfVanishingData_of_isInvertible`: **the content of Tag
  02SF for an invertible module.** A meromorphic section has a coordinate with respect to some
  generator of `L_ξ`, and one integer is the order of that coordinate for every generator;
  packaged with the quasi-coherence witness, as the tag's definition is.
* `AlgebraicGeometry.orderOfVanishingDataOfInvertible` and
  `AlgebraicGeometry.orderOfVanishingOfInvertible`: that integer and its characterization.
* `AlgebraicGeometry.constantGenericStalkOfGlobalSection` and
  `AlgebraicGeometry.orderOfVanishingOfGlobalSection`: a genuine global section read as a
  meromorphic section, and its order of vanishing.

## Implementation notes

The hypothesis on `ξ` is written `codimension (IrreducibleCloseds.closureSingleton ξ) = 1`,
which is the condition the generic point of a prime divisor satisfies by definition, rather than
`Order.coheight ξ = 1`, which is the form Mathlib's `AlgebraicGeometry.Scheme.ord` wants. The two
are the same because `TopologicalSpace.irreducibleSetEquivPoints` is an order isomorphism between
the points of a sober `T0` space and its irreducible closed subsets, and coheight is invariant
under an order isomorphism (`Order.coheight_orderIso`); a scheme is sober and `T0`.

Invertibility is `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, the class the Tag 0B8M
trivialization is stated for. It is written with the arguments `X.sheaf.obj` and
`X.ringCatSheaf.property`; because `Stacks.SheafOfModules.TensorSheafification.structureSheaf` is a
  plain `def` while
`structureSheafRing` is `@[reducible]`, that spelling
  does not discharge the
library's `IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property` by instance
search, so each use carries the one-line `have` bridge; the two are interchangeable by `exact`.

The remaining distance to the statement of Tag 02SF is the meromorphic section itself. The
section enters only as the global section `t` of the constant generic-stalk module sheaf that
Tag 01X5 part (2) attaches to it, so `t` is a parameter here;
`StacksFrontier/AlgebraicGeometry/Divisors/OrderOfVanishingMeromorphic.lean` instantiates it at
the image of the section under `AlgebraicGeometry.meromorphicSectionSheafIsoConstant` and
reaches the statement of Tag 02SF.

**A genuine global section is not a meromorphic section until it is made one.**
`orderOfVanishingOfInvertible` takes a global section of `constantGenericStalkModuleSheaf X L`,
not an element of `Γ(L, ⊤)` and a point; `constantGenericStalkOfGlobalSection` is the map that
has to be inserted, the constant section of the germ at the generic point. Its only publicly
available predecessor was private to
`StacksFrontier/AlgebraicGeometry/Divisors/MeromorphicSectionsConstant.lean`.

## References

* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 02I3](https://stacks.math.columbia.edu/tag/02I3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry

/-! ### Coheight of a point and codimension of the closure of its singleton -/

/-- For a point of a scheme, the coheight in the specialization order is the codimension of the
closure of its singleton: `TopologicalSpace.irreducibleSetEquivPoints` is an order isomorphism
and coheight is invariant under one. -/
theorem coheight_eq_codimension_closureSingleton {X : Scheme.{u}} (ξ : X) :
    Order.coheight ξ = codimension (IrreducibleCloseds.closureSingleton ξ) :=
  (Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm ξ).symm

/-- A point of a scheme has coheight one exactly when the closure of its singleton has
codimension one. The right-hand side is the condition imposed on the generic point of a prime
divisor in Tag 0BE2; the left-hand side is the form `AlgebraicGeometry.Scheme.ord` wants. -/
theorem coheight_eq_one_iff_codimension_closureSingleton_eq_one {X : Scheme.{u}} (ξ : X) :
    Order.coheight ξ = 1 ↔ codimension (IrreducibleCloseds.closureSingleton ξ) = 1 := by
  rw [coheight_eq_codimension_closureSingleton]

/-! ### The order of vanishing for an invertible module -/

/-- **Stacks 02SF, the content of the definition, for an invertible module.** Let `X` be a
locally Noetherian integral scheme, `L` an invertible sheaf of `𝒪_X`-modules and `ξ` a point
whose closure has codimension one — the generic point of a prime divisor. Then a meromorphic
section `t` of `L` — a global section of the constant generic-stalk module sheaf — has a
coordinate with respect to every generator of `L_ξ`, and the order of that coordinate in
`𝒪_{X, ξ}` is one and the same integer whatever generator is used. The quasi-coherence of `L`,
which the definition of the tag records alongside the integer, is a consequence of
invertibility.

The generator of `L_ξ` is produced from invertibility by the trivialization of Tag 0B8M:
`Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible` gives a neighbourhood of `ξ`
carrying a section by which multiplication is bijective over that open set and over every
smaller one, which is the hypothesis of
`AlgebraicGeometry.nonempty_orderOfVanishingData_of_bijective_smul`. -/
theorem nonempty_orderOfVanishingData_of_isInvertible
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (ξ : X) (hξ : codimension (IrreducibleCloseds.closureSingleton ξ) = 1)
    (t : (constantGenericStalkModuleSheaf X L).val.obj (op ⊤)) :
    Nonempty { q : PSigma (fun _ : L.IsQuasicoherent => ℤ) //
      letI : L.IsQuasicoherent := q.1
      let R := X.presheaf.stalk ξ
      let K := X.functionField
      letI : Module R (L.presheaf.stalk ξ) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val ξ
      letI : Module K (L.presheaf.stalk (genericPoint X)) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val (genericPoint X)
      let isCoordinate := fun (m : L.presheaf.stalk ξ) (a : K) =>
        t = constantGenericStalkModuleSection X L ⊤
          (a • (L.presheaf.stalkSpecializes
            ((genericPoint_spec X).specializes trivial)) m)
      (∃ m : L.presheaf.stalk ξ,
        (Submodule.span R {m} = ⊤) ∧ (∃ a : K, isCoordinate m a)) ∧
      (∀ (m : L.presheaf.stalk ξ)
        (_ : Submodule.span R {m} = ⊤) (a : K),
        isCoordinate m a → q.2 = X.ord a ξ) } := by
  classical
  have hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L := ‹_›
  have hqc : L.IsQuasicoherent :=
    Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible X L
  have hcoh : Order.coheight ξ = 1 :=
    (coheight_eq_one_iff_codimension_closureSingleton_eq_one ξ).2 hξ
  have hlocal : ∀ z : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace z) :=
    fun z => X.isLocalRing z
  obtain ⟨U, hξU, s, hs⟩ :=
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := X.toRingedSpace) L ξ
  obtain ⟨d, hd⟩ :=
    nonempty_orderOfVanishingData_of_bijective_smul X L ξ hcoh U hξU s hs t
  exact ⟨⟨⟨hqc, d⟩, hd⟩⟩

/-- **Stacks 02SF for an invertible module.** The order of vanishing of a meromorphic section
along a point whose closure has codimension one, together with its characterization by the order
of a coordinate with respect to any generator of the stalk, and the quasi-coherence of `L`. A
choice of the data provided by
`AlgebraicGeometry.nonempty_orderOfVanishingData_of_isInvertible`. -/
def orderOfVanishingDataOfInvertible
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (ξ : X) (hξ : codimension (IrreducibleCloseds.closureSingleton ξ) = 1)
    (t : (constantGenericStalkModuleSheaf X L).val.obj (op ⊤)) :
    { q : PSigma (fun _ : L.IsQuasicoherent => ℤ) //
      letI : L.IsQuasicoherent := q.1
      let R := X.presheaf.stalk ξ
      let K := X.functionField
      letI : Module R (L.presheaf.stalk ξ) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val ξ
      letI : Module K (L.presheaf.stalk (genericPoint X)) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val (genericPoint X)
      let isCoordinate := fun (m : L.presheaf.stalk ξ) (a : K) =>
        t = constantGenericStalkModuleSection X L ⊤
          (a • (L.presheaf.stalkSpecializes
            ((genericPoint_spec X).specializes trivial)) m)
      (∃ m : L.presheaf.stalk ξ,
        (Submodule.span R {m} = ⊤) ∧ (∃ a : K, isCoordinate m a)) ∧
      (∀ (m : L.presheaf.stalk ξ)
        (_ : Submodule.span R {m} = ⊤) (a : K),
        isCoordinate m a → q.2 = X.ord a ξ) } :=
  Classical.choice (nonempty_orderOfVanishingData_of_isInvertible X L ξ hξ t)

/-- **Stacks 02SF for an invertible module.** The order of vanishing along `ξ` of a meromorphic
section `t` of an invertible module `L`. It is characterized by
`AlgebraicGeometry.orderOfVanishingDataOfInvertible`: it is the order of the coordinate of `t`
with respect to any generator of `L_ξ`. -/
def orderOfVanishingOfInvertible
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (ξ : X) (hξ : codimension (IrreducibleCloseds.closureSingleton ξ) = 1)
    (t : (constantGenericStalkModuleSheaf X L).val.obj (op ⊤)) : ℤ :=
  (orderOfVanishingDataOfInvertible X L ξ hξ t).val.2

/-! ### The order of vanishing of a genuine global section -/

/-- A global section of `F` read as a meromorphic section: the constant section of its germ at
the generic point. -/
def constantGenericStalkOfGlobalSection (X : Scheme.{u}) [IsIntegral X] (F : X.Modules)
    (s : F.val.obj (op ⊤)) : (constantGenericStalkModuleSheaf X F).val.obj (op ⊤) :=
  constantGenericStalkModuleSection X F ⊤
    (F.presheaf.germ ⊤ (genericPoint X) (Set.mem_univ _) s)

/-- The element of the generic stalk that a global section becomes is its germ there: the
representation of `AlgebraicGeometry.exists_unique_eq_constantGenericStalkModuleSection` is the
expected one. -/
theorem germ_eq_of_constantGenericStalkOfGlobalSection_eq (X : Scheme.{u}) [IsIntegral X]
    (F : X.Modules) (s : F.val.obj (op ⊤)) (m : F.presheaf.stalk (genericPoint X))
    (h : constantGenericStalkOfGlobalSection X F s =
      constantGenericStalkModuleSection X F ⊤ m) :
    F.presheaf.germ ⊤ (genericPoint X) (Set.mem_univ _) s = m := by
  obtain ⟨m₀, _, huniq⟩ :=
    exists_unique_eq_constantGenericStalkModuleSection X F
      (constantGenericStalkOfGlobalSection X F s)
  exact (huniq _ rfl).symm.trans (huniq m h)

/-- **The order of vanishing of a global section of an invertible module** along a point of
codimension one: `AlgebraicGeometry.orderOfVanishingOfInvertible` at the meromorphic section
the global section determines.

This is the form the determinant comparison of [Stacks, Tag 0B3T] is measured in — the
comparison map is a genuine morphism of invertible modules, hence a global section of the twist,
not a meromorphic section given in advance. -/
def orderOfVanishingOfGlobalSection
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (ξ : X) (hξ : codimension (IrreducibleCloseds.closureSingleton ξ) = 1)
    (s : L.val.obj (op ⊤)) : ℤ :=
  orderOfVanishingOfInvertible X L ξ hξ (constantGenericStalkOfGlobalSection X L s)

end AlgebraicGeometry

end
