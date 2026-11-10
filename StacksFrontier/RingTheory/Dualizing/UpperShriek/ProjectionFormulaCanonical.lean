module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalComparisonBridge

/-!
# The two coherences of [stacks 0E2H] are one coherence of the lax monoidal structure map

`StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalComparisonBridge` reduces the invertibility
that [stacks 0E2H] needs to two named inputs:
`Dualizing.ProjectionFormula.ProjCounitCompat` -- the compatibility of the projection formula
with the counit of [stacks 0GMT] -- and
`Dualizing.ProjectionFormula.ProjTensorBaseChangeCompat`, a coherence in which neither counit nor
any object of `D(B)` occurs.

This file measures how the second depends on the first, and the answer is: entirely.

`Dualizing.ProjectionFormula.projCounitCompatAt_iff_inv_eq` says that `ProjCounitCompat` at a pair
`(N, G)` holds exactly when the inverse projection formula there is
`Dualizing.ProjectionFormula.canonicalProjInv`, the morphism the two adjunctions produce on their
own.  `ProjTensorBaseChangeCompat` mentions the projection formula at exactly three pairs -- at
`(M ⊗ᴸ_A Y, 1_B)` and `(M, 1_B)` through
`Dualizing.ProjectionFormula.restrictExtendIso`, and at `(Y, Ext M)` directly -- so once
`ProjCounitCompat` is known at those three pairs, every projection formula in
`ProjTensorBaseChangeCompat` can be replaced by `canonicalProjInv`, and what is left mentions
only the unit and the counit of [stacks 0GMT], the section
`Dualizing.derivedTensorBaseChangeSection` of the lax monoidal structure map, and the unitor,
symmetry and associator of [stacks 0A63].

## Main results

* `Dualizing.ProjectionFormula.canonicalRestrictExtendInv` -- the canonical candidate for the
  inverse of `Dualizing.ProjectionFormula.restrictExtendIso`: the projection morphism of
  `canonicalProjInv` at the tensor unit of `D(B)`, between the symmetry and the left unitor.
* `Dualizing.ProjectionFormula.restrictExtendIso_inv_app_eq` -- **`restrictExtendIso` is
  canonical as soon as `ProjCounitCompat` holds at the tensor unit of `D(B)`.**  Only the single
  object `1_B` of `D(B)` is needed, not the whole of `ProjCounitCompat`.
* `Dualizing.ProjectionFormula.projTensorBaseChangeCompat_iff_inv` -- **the coherence with every
  projection formula read backwards**, with no isomorphism inverted on the right: an
  unconditional restatement, obtained by cancelling the two isomorphisms that sat on the right of
  the composite.
* `Dualizing.ProjectionFormula.CanonicalProjTensorBaseChangeCompat` -- the same coherence with
  `canonicalProjInv` in place of the projection formula.  **The projection formula does not occur
  in it**: it is an identity between two morphisms
  `(M ⊗ᴸ_A Y) ⊗ᴸ_A T ⟶ i_*(Ext M ⊗ᴸ_B Ext Y)` built from the unit and the counit of
  [stacks 0GMT], the section `ν` of the lax monoidal structure map `μ` of derived base change,
  and the symmetric monoidal structure of [stacks 0A63].
* `Dualizing.ProjectionFormula.projTensorBaseChangeCompat_iff_canonical` -- **the reduction**:
  given `ProjCounitCompat` at the three pairs listed above, `ProjTensorBaseChangeCompat` holds
  exactly when `CanonicalProjTensorBaseChangeCompat` does.
* `Dualizing.ProjectionFormula.isIso_restrict_derivedTensorHomDiagonalAlongRingHom_of_canonical`
  -- hence **the invertibility [stacks 0E2H] needs, on `ProjCounitCompat` and the coherence of
  the structure map**, with `ProjTensorBaseChangeCompat` no longer mentioned.

## What this says about the residue of [stacks 0E2H]

The two inputs of [stacks 0E2H] are therefore *not* two independent unknowns about the projection
formula.  Modulo `ProjCounitCompat` -- which is itself the single statement that the projection
formula is the canonical projection morphism, by
`Dualizing.ProjectionFormula.projCounitCompat_iff_inv_eq` -- the second input is a coherence of
`ν` alone: reading both sides of `CanonicalProjTensorBaseChangeCompat` out, each is the unit of
[stacks 0GMT] followed by derived restriction of a composite of two instances of `ν` and one
counit, and the equation between them is exactly the compatibility of `ν` with the associator and
the symmetry, that is the *monoidality* of derived base change rather than its lax structure map
at a single pair.  Nothing in this library proves that: `Dualizing.derivedTensorBaseChange` is
constructed as a mate in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMate` and inverted in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeStrong`, and neither its
associativity nor its unitality is recorded anywhere.

So the residue of [stacks 0E2H] after this file is: `ProjCounitCompat`, and the associativity of
the lax monoidal structure map.  Nothing here discharges either.

`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaEvaluation` carries that second
residue as far as the adjunctions go: it removes `ν` from the canonical projection morphism
altogether (`Dualizing.ProjectionFormula.canonicalProjInv_eq`, which exhibits `ω` as the
transpose of restricted coevaluation followed by the component of [stacks 0E1W]), and it transposes
`CanonicalProjTensorBaseChangeCompat` into one equation in `D(B)` with no unit, no restriction
functor and no internal Hom in it,
`Dualizing.ProjectionFormula.CanonicalTensorBaseChangeCoherence`, by
`Dualizing.ProjectionFormula.canonicalProjTensorBaseChangeCompat_iff_coherence`.  What that file
also measures is that the sentence above -- "neither its associativity nor its unitality is
recorded anywhere" -- was true of the statement and is no longer: the coherence now has a name.
It is still unproved, and the file measures why: in that shape it is the compatibility of
[stacks 0E1W] with the currying isomorphism of [stacks 0A65], whose *evaluation* half is free
(`Dualizing.ProjectionFormula.canonicalProjInv_comp_restrict_evaluation`) and whose currying half
is equivalent to the associativity of `μ`.  That last equivalence is itself a theorem now,
`Dualizing.derivedTensorBaseChangeAssoc_iff_curryCompat` of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.CurryingCoherence`, so the currying half
has a name on both sides.

No `@[stacks]` attribute is placed here: nothing in this file is unconditional, and the
identities it proves belong to the tags of the morphisms they are about.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom

universe u v

namespace Dualizing.ProjectionFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Two isomorphisms cancelled off the right of a four-fold composite. -/
private theorem comp_cancel_iff {C : Type*} [Category* C] {V W X Y Z : C}
    (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y) (c' : Y ⟶ X) (d : Y ⟶ Z) (d' : Z ⟶ Y) (S : V ⟶ Z)
    (hc : c ≫ c' = 𝟙 X) (hc' : c' ≫ c = 𝟙 Y)
    (hd : d ≫ d' = 𝟙 Y) (hd' : d' ≫ d = 𝟙 Z) :
    a ≫ b ≫ c ≫ d = S ↔ a ≫ b = S ≫ d' ≫ c' := by
  constructor
  · rintro rfl
    simp [reassoc_of% hd, hc]
  · intro h
    rw [← Category.assoc a b, h]
    simp [reassoc_of% hc', hd']

/-! ### The identification of the algebra with restricted extension of scalars, canonically -/

/-- **The canonical candidate for the inverse of
`Dualizing.ProjectionFormula.restrictExtendIso`.**  Writing `T = i_*(1_B)` for the algebra and
`Ext` for the model `E`, this is the composite

`N ⊗ᴸ_A T --swap--> T ⊗ᴸ_A N --canonicalProjInv--> i_*(1_B ⊗ᴸ_B Ext N) --i_*(unitor)-->
i_*(Ext N)`,

built from the unit and the counit of [stacks 0GMT] and the section
`Dualizing.derivedTensorBaseChangeSection` of the lax monoidal structure map alone: the
projection formula does not occur in it.  `restrictExtendIso` is this morphism exactly when
`Dualizing.ProjectionFormula.ProjCounitCompatAt` holds at the tensor unit of `D(B)`; see
`Dualizing.ProjectionFormula.restrictExtendIso_inv_app_eq`. -/
noncomputable def canonicalRestrictExtendInv (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
        (N, restrictedAlgebra.{u, max u v}
          (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory) ⟶
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj (E.functor.obj N) :=
  ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap
      (restrictedAlgebra.{u, max u v}
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory) N).inv ≫
    canonicalProjInv.{u, v} φ E N (derivedTensorUnit.{u, max u v, max u v + 1} B) ≫
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
        (derivedTensorUnitLeft.{u, max u v, max u v + 1} B (E.functor.obj N)).hom

/-- **The identification of restricted derived extension of scalars with tensoring by the algebra
is canonical as soon as the owed coherence holds at the tensor unit.**  `restrictExtendIso` is
built from the projection formula at the single object `1_B` of `D(B)`, so
`Dualizing.ProjectionFormula.ProjCounitCompatAt` there -- and not the whole of
`Dualizing.ProjectionFormula.ProjCounitCompat` -- already pins its inverse to
`Dualizing.ProjectionFormula.canonicalRestrictExtendInv`. -/
theorem restrictExtendIso_inv_app_eq (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (h : ProjCounitCompatAt.{u, v} φ E adj N
      (derivedTensorUnit.{u, max u v, max u v + 1} B)) :
    (restrictExtendIso.{u, max u v} φ E
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory adj).inv.app N =
      canonicalRestrictExtendInv.{u, v} φ E N := by
  dsimp only [canonicalRestrictExtendInv]
  rw [← (projCounitCompatAt_iff_inv_eq.{u, v} φ E adj N _).mp h]
  simp only [restrictExtendIso, NatIso.ofComponents_inv_app, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Category.assoc, Iso.app_inv]

/-! ### The monoidal coherence with every projection formula read backwards -/

/-- **`Dualizing.ProjectionFormula.ProjTensorBaseChangeCompat` with the two isomorphisms on the
right cancelled.**  The coherence asserts that a four-fold composite is the symmetry
rearrangement; its last two factors are isomorphisms, so it says equally that the first two
factors are the rearrangement followed by the inverses of the last two.  That is the shape in
which the projection formula occurs only through its *inverse*, which is the direction
`Dualizing.ProjectionFormula.projCounitCompatAt_iff_inv_eq` computes.

Unconditional: no coherence is assumed. -/
theorem projTensorBaseChangeCompat_iff_inv (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (Y M : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjTensorBaseChangeCompat.{u, v} φ E adj Y M ↔
      (restrictExtendIso.{u, max u v} φ E
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory adj).inv.app
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y)) ≫
          (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
            (Dualizing.derivedTensorBaseChangeSection.{u, u, v} φ E.functor
              (modelComparison.{u, v} φ E) M Y) =
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
              (X := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y),
                restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
              (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (Y, M),
                restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
              (((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap M Y).hom,
                𝟙 (restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)) ≫
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorAssoc Y M
              (restrictedAlgebra.{u, max u v}
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)).hom ≫
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap Y
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
                (M, restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))).hom) ≫
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
              (X := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
                (M, restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory), Y))
              (Y := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
                (E.functor.obj M), Y))
              ((restrictExtendIso.{u, max u v} φ E
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory adj).inv.app M,
                𝟙 Y) ≫
            (derivedProjNatIso.{u, max u v} φ E
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory adj Y).inv.app
              (E.functor.obj M) := by
  dsimp only [ProjTensorBaseChangeCompat]
  refine comp_cancel_iff _ _ _ _ _ _ _ (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _) ?_ ?_ <;>
  · rw [← Functor.map_comp]
    simp

/-! ### The coherence with no projection formula in it -/

/-- **The monoidal coherence of [stacks 0E2H] with the projection formula replaced by the
canonical projection morphism.**  Writing `T = i_*(1_B)`, `Ext` for the model `E`, `η` and `ε`
for the unit and the counit of [stacks 0GMT] and `ν` for
`Dualizing.derivedTensorBaseChangeSection`, this is the equation

`c_{M ⊗ᴸ_A Y} ≫ i_*(ν_{M, Y}) = (rearrangement) ≫ (c_M ⊗ᴸ_A 𝟙_Y) ≫ canonicalProjInv_{Y, Ext M}`

of morphisms `(M ⊗ᴸ_A Y) ⊗ᴸ_A T ⟶ i_*(Ext M ⊗ᴸ_B Ext Y)`, with `c` for
`Dualizing.ProjectionFormula.canonicalRestrictExtendInv` and `rearrangement` the symmetry and
associativity composite of [stacks 0A63] that `ProjTensorBaseChangeCompat` has on its right.

**The projection formula does not occur**: unfolding `canonicalRestrictExtendInv` and
`Dualizing.ProjectionFormula.canonicalProjInv`, each side is `η` followed by derived restriction
of a composite of instances of `ν` and `ε`, between unitors and symmetries.  So this is a
coherence of the lax monoidal structure map of derived base change alone -- its compatibility
with the associator -- and not a statement about the projection formula at all.  See
`Dualizing.ProjectionFormula.projTensorBaseChangeCompat_iff_canonical`. -/
def CanonicalProjTensorBaseChangeCompat (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (Y M : DerivedCategory (ModuleCat.{max u v} A)) : Prop :=
  canonicalRestrictExtendInv.{u, v} φ E
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y)) ≫
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
        (Dualizing.derivedTensorBaseChangeSection.{u, u, v} φ E.functor
          (modelComparison.{u, v} φ E) M Y) =
    ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y),
            restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
          (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (Y, M),
            restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
          (((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap M Y).hom,
            𝟙 (restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)) ≫
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorAssoc Y M
          (restrictedAlgebra.{u, max u v}
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)).hom ≫
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap Y
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
            (M, restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))).hom) ≫
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
            (M, restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory), Y))
          (Y := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            (E.functor.obj M), Y))
          (canonicalRestrictExtendInv.{u, v} φ E M, 𝟙 Y) ≫
        canonicalProjInv.{u, v} φ E Y (E.functor.obj M)

/-- **The reduction: the second input of [stacks 0E2H] is a coherence of the lax monoidal
structure map, modulo the first.**  `Dualizing.ProjectionFormula.ProjTensorBaseChangeCompat`
mentions the projection formula at exactly three pairs -- at `(M ⊗ᴸ_A Y, 1_B)` and `(M, 1_B)`
through `Dualizing.ProjectionFormula.restrictExtendIso`, and at `(Y, Ext M)` directly -- and
`Dualizing.ProjectionFormula.ProjCounitCompatAt` at those three pairs replaces each of them by
`Dualizing.ProjectionFormula.canonicalProjInv`.  What is left is
`Dualizing.ProjectionFormula.CanonicalProjTensorBaseChangeCompat`, in which the projection
formula does not occur.

So the two inputs of [stacks 0E2H] are not independent: granted the first at three pairs, the
second is a statement about `Dualizing.derivedTensorBaseChangeSection` and the symmetric
monoidal structure of [stacks 0A63] alone. -/
theorem projTensorBaseChangeCompat_iff_canonical (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (Y M : DerivedCategory (ModuleCat.{max u v} A))
    (h₁ : ProjCounitCompatAt.{u, v} φ E adj
      ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y))
      (derivedTensorUnit.{u, max u v, max u v + 1} B))
    (h₂ : ProjCounitCompatAt.{u, v} φ E adj M
      (derivedTensorUnit.{u, max u v, max u v + 1} B))
    (h₃ : ProjCounitCompatAt.{u, v} φ E adj Y (E.functor.obj M)) :
    ProjTensorBaseChangeCompat.{u, v} φ E adj Y M ↔
      CanonicalProjTensorBaseChangeCompat.{u, v} φ E Y M := by
  rw [projTensorBaseChangeCompat_iff_inv.{u, v} φ E adj Y M,
    restrictExtendIso_inv_app_eq.{u, v} φ E adj _ h₁,
    restrictExtendIso_inv_app_eq.{u, v} φ E adj M h₂,
    (projCounitCompatAt_iff_inv_eq.{u, v} φ E adj Y _).mp h₃]
  exact Iff.rfl

/-- **The second input of [stacks 0E2H] from the first and the coherence of the structure map.**
The implication of `Dualizing.ProjectionFormula.projTensorBaseChangeCompat_iff_canonical` in the
direction the bridge consumes. -/
theorem projTensorBaseChangeCompat_of_canonical (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (Y M : DerivedCategory (ModuleCat.{max u v} A))
    (h₁ : ProjCounitCompatAt.{u, v} φ E adj
      ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y))
      (derivedTensorUnit.{u, max u v, max u v + 1} B))
    (h₂ : ProjCounitCompatAt.{u, v} φ E adj M
      (derivedTensorUnit.{u, max u v, max u v + 1} B))
    (h₃ : ProjCounitCompatAt.{u, v} φ E adj Y (E.functor.obj M))
    (h : CanonicalProjTensorBaseChangeCompat.{u, v} φ E Y M) :
    ProjTensorBaseChangeCompat.{u, v} φ E adj Y M :=
  (projTensorBaseChangeCompat_iff_canonical.{u, v} φ E adj Y M h₁ h₂ h₃).mpr h

/-! ### What [stacks 0E2H] needs, on the first coherence and the structure map alone -/

/-- **The invertibility that [stacks 0E2H] needs, from the owed coherence at every pair and the
coherence of the lax monoidal structure map.**  This is
`isIso_restrict_derivedTensorHomDiagonalAlongRingHom_of_projCounitCompatAt` with its second
input, `ProjTensorBaseChangeCompat`, replaced by `CanonicalProjTensorBaseChangeCompat` -- in which
the projection formula does not occur -- at the cost of taking `ProjCounitCompat` at every object
of `D(A)` rather than at the single one the bridge asks for.

So the whole residue of [stacks 0E2H] at this point is two statements about *different* things:
the compatibility of the projection formula with the counit of [stacks 0GMT], which is a
comparison of a chain-level construction with an adjunction-level one, and a coherence of
`Dualizing.derivedTensorBaseChangeSection` with the symmetric monoidal structure of
[stacks 0A63], in which the projection formula plays no part. -/
theorem isIso_restrict_derivedTensorHomDiagonalAlongRingHom_of_canonical (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (Y X : DerivedCategory (ModuleCat.{max u v} A))
    (hP : ∀ N : DerivedCategory (ModuleCat.{max u v} A), ProjCounitCompat.{u, v} φ E adj N)
    (hC : CanonicalProjTensorBaseChangeCompat.{u, v} φ E Y
      ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
        ((Dualizing.derivedHom.{u, max u v, u} φ).obj X)))
    (hdiag : IsIso (Dualizing.derivedTensorHomDiagonalOverRing.{u, max u v} Y X
      (restrictedAlgebra.{u, max u v}
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))) :
    IsIso ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
      ((derivedTensorHomDiagonalAlongRingHom.{u, max u v} φ E _ adj Y).app X)) :=
  isIso_restrict_derivedTensorHomDiagonalAlongRingHom_of_projCounitCompatAt.{u, v} φ E adj Y X
    (projTensorBaseChangeCompat_of_canonical.{u, v} φ E adj Y _
      (hP _ _) (hP _ _) (hP _ _) hC)
    (hP Y _) hdiag

end Dualizing.ProjectionFormula

end
