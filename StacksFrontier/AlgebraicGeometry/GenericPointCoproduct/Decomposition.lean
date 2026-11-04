module

public import StacksFrontier.AlgebraicGeometry.GenericPointCoproduct.Basic
public import StacksFrontier.AlgebraicGeometry.GenericPointProduct.Decomposition

/-!
# The generic-point direct sum on a reduced or a locally Noetherian scheme

The displayed formula of the source gives the sheaf of meromorphic functions both as a direct sum
and as a product over the generic points of the irreducible components. The product half is
in the library; this file supplies the direct-sum half, which the source's own proof obtains from it by
the single observation that *"a locally finite direct sum of sheaves of modules is equal to the
product"*.

## Main results

All three are in the namespace `Stacks.AlgebraicGeometry.GenericPointCoproduct`.

* `nonempty_coproductIso_product_genericPointStalkModule`: the coproduct and the product of the
  generic-point contributions agree, for any scheme whose quasi-compact opens have finitely many
  irreducible components.
* `meromorphicFunctions_iso_coproduct_genericPointStalks`: the direct-sum decomposition on a
  reduced scheme.
* `meromorphicFunctions_iso_coproduct_of_noEmbeddedPoints`: the direct-sum decomposition on a
  locally Noetherian scheme without embedded points.

## Implementation notes

Neither hypothesis of the tagged statements is used for the coproduct-to-product comparison itself: reducedness, and
the absence of embedded points, enter only through the product decomposition they already
support. The comparison needs just the local finiteness of the irreducible components, which on a
locally Noetherian scheme is automatic.

The two examples at the end of this file restate the two tagged results with every auxiliary constant of
the statements replaced by its own defining expression, in the binder order of the statements.
The embedded-point predicate is inlined down to `Stacks.Divisors.IsAssociatedPoint`, which is
the associated-point predicate of the statement of Tag 02OJ, with the same module structure on
the stalk; the
statement supplies that structure by a `letI` because, as `StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints.lean`
records, typeclass resolution does not find it for an `X.Modules` without the restatement
`AlgebraicGeometry.Scheme.Modules.moduleStalk`.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GenericPointCoproduct

open Stacks.AlgebraicGeometry.GenericPointDecomposition
open Stacks.AlgebraicGeometry.GenericPointGluing

/-- The generic-point contribution has no sections on an open set of a subscheme missing that
point, so its restriction to an open set missing the point is a zero object. -/
theorem isZero_restrict_genericPointStalkModule {X : Scheme.{u}} (V : X.Opens)
    (η : genericPoints X) (hη : (η : X) ∉ V) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (genericPointStalkModule X η)) := by
  refine isZero_of_subsingleton_sections _ fun W ↦ ?_
  have hnot : (η : X) ∉ V.ι ''ᵁ W := fun h ↦ hη (Scheme.Opens.ι_image_le V W h)
  have h : Subsingleton Γ(genericPointStalkModule X η, V.ι ''ᵁ W) :=
    MeromorphicQuasicoherent.subsingleton_genericPointStalkModule_sections hnot
  exact h

/-- **The generic-point family is locally finite, so its coproduct is its product.** On an
affine open only the finitely many generic points lying in that open contribute, and there a
coproduct of a family with all but finitely many members zero is the product of that family;
being an isomorphism is local on the base. No hypothesis on the weakly associated points is
needed, only the local finiteness of the irreducible components. -/
theorem nonempty_coproductIso_product_genericPointStalkModule (X : Scheme.{u})
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    Nonempty ((∐ fun η : genericPoints X ↦ genericPointStalkModule X η) ≅
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModule X η) := by
  classical
  have hiso : IsIso (Sigma.desc (Pi.ι fun η : genericPoints X ↦
      genericPointStalkModule X η)) := by
    refine AffineBaseChange.isIso_of_isIso_restrict _ (fun V : X.affineOpens ↦ (V : X.Opens))
      (IsOpenCover.mk (iSup_affineOpens_eq_top X)) fun V ↦ ?_
    have _ := (Scheme.Modules.restrictAdjunction (V : X.Opens).ι).leftAdjoint_preservesColimits
    have _ := preservesLimit_discrete_restrictFunctor (V : X.Opens)
      (fun η : genericPoints X ↦ genericPointStalkModule X η)
    refine isIso_map_coproductToProduct_of_finite _ _ (Set.Finite.subset
      (Set.finite_coe_iff.mp (finite_genericPoints_subtype X (hfin (V : X.Opens) V.2.isCompact)))
      fun η hη ↦ ?_)
    by_contra hmem
    exact hη (isZero_restrict_genericPointStalkModule (V : X.Opens) η hmem)
  exact ⟨@asIso _ _ _ _ _ hiso⟩

/-- **Stacks Project, Tag 02OW.** On a reduced scheme whose quasi-compact opens have finitely
many irreducible components, the `𝒪_X`-module of meromorphic functions is the direct sum, over
the generic points of the irreducible components, of the structure sheaves of the local schemes
there, pushed forward to `X`. -/
@[stacks 02OW "generic-point direct sum"]
theorem meromorphicFunctions_iso_coproduct_genericPointStalks (X : Scheme.{u}) [IsReduced X]
    (hfinite : GenericPointProduct.FiniteComponentsOnCompactOpens X) :
    Nonempty (meromorphicFunctions X ≅
      ∐ fun η : genericPoints X ↦ genericPointStalkModule X η) :=
  ⟨(GenericPointProduct.meromorphicFunctions_iso_product_genericPointStalks X hfinite).some ≪≫
    (nonempty_coproductIso_product_genericPointStalkModule X hfinite).some.symm⟩

/-- **Stacks Project, Tag 0EMH.** On a locally Noetherian scheme without embedded points, the
`𝒪_X`-module of meromorphic functions is the direct sum, over the generic points of the
irreducible components, of the structure sheaves of the local schemes there, pushed forward to
`X`. -/
@[stacks 0EMH "meromorphic functions as a direct sum"]
theorem meromorphicFunctions_iso_coproduct_of_noEmbeddedPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : AlgebraicGeometry.HasNoEmbeddedPoints X) :
    Nonempty (meromorphicFunctions X ≅
      ∐ fun η : genericPoints X ↦ genericPointStalkModule X η) :=
  ⟨(GenericPointProduct.meromorphicFunctions_iso_product_of_noEmbeddedPoints X hX).some ≪≫
    (nonempty_coproductIso_product_genericPointStalkModule X
      (GenericPointProduct.finiteComponentsOnCompactOpens_of_isLocallyNoetherian X)).some.symm⟩

/-! ### Faithfulness to the tagged statements -/

/-- Stacks Tag 02OW, label `generic-point direct sum`, in the binder order of the statement and
with every auxiliary constant replaced by its own defining expression. -/
example (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Nonempty ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat RingCat.{u})).map
            (⟨X.presheaf.toTotalQuotientPresheaf ≫
              toSheafify (Opens.grothendieckTopology X)
                X.presheaf.totalQuotientPresheaf⟩ :
              X.sheaf ⟶ (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
                X.presheaf.totalQuotientPresheaf))).obj
        (SheafOfModules.unit
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat RingCat.{u})).obj
              ((presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
                X.presheaf.totalQuotientPresheaf))) ≅
      ∐ fun η : genericPoints X ↦
        (Scheme.Modules.pushforward (X.fromSpecStalk η.1)).obj
          (SheafOfModules.unit (Spec (X.presheaf.stalk η.1)).ringCatSheaf)) :=
  meromorphicFunctions_iso_coproduct_genericPointStalks X hfinite

/-- Stacks Tag 0EMH, label `meromorphic functions as a direct sum`, in the binder order of the
statement and with every auxiliary constant replaced by its own defining expression. -/
example (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : ∀ x : X, ¬ (Stacks.Divisors.IsAssociatedPoint
        (SheafOfModules.unit X.ringCatSheaf) x ∧
      ∃ x' : X, Stacks.Divisors.IsAssociatedPoint
        (SheafOfModules.unit X.ringCatSheaf) x' ∧ x' ⤳ x ∧ x' ≠ x)) :
    Nonempty ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat RingCat.{u})).map
            (⟨X.presheaf.toTotalQuotientPresheaf ≫
              toSheafify (Opens.grothendieckTopology X)
                X.presheaf.totalQuotientPresheaf⟩ :
              X.sheaf ⟶ (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
                X.presheaf.totalQuotientPresheaf))).obj
        (SheafOfModules.unit
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat RingCat.{u})).obj
              ((presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
                X.presheaf.totalQuotientPresheaf))) ≅
      ∐ fun η : genericPoints X ↦
        (Scheme.Modules.pushforward (X.fromSpecStalk η.1)).obj
          (SheafOfModules.unit (Spec (X.presheaf.stalk η.1)).ringCatSheaf)) :=
  meromorphicFunctions_iso_coproduct_of_noEmbeddedPoints X hX

/-- The absence-of-embedded-points hypothesis of the statement, inlined, is the library's predicate. -/
example (X : Scheme.{u}) :
    (∀ x : X, ¬ (Stacks.Divisors.IsAssociatedPoint
        (SheafOfModules.unit X.ringCatSheaf) x ∧
      ∃ x' : X, Stacks.Divisors.IsAssociatedPoint
        (SheafOfModules.unit X.ringCatSheaf) x' ∧ x' ⤳ x ∧ x' ≠ x)) ↔
      AlgebraicGeometry.HasNoEmbeddedPoints X := Iff.rfl

end Stacks.AlgebraicGeometry.GenericPointCoproduct

end
