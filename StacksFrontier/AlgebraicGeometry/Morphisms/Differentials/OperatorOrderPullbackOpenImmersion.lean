module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OperatorOrderOpenImmersion
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperatorsCoefficientIso

/-!
# The order of a differential operator for the inverse image across an open immersion

Let `j : Z ⟶ W` be an open immersion of schemes and `p : W ⟶ Y` a morphism. The restriction of a
module on `W` along `j` is isomorphic to its inverse image along `j`, so an operator on the local
sections of modules on `W`, defined over the opens contained in the image of `j`, is a differential
operator of order at most `k` on `W/Y` exactly when the corresponding global operator on the
inverse images is a differential operator of order at most `k` on `Z/Y`. This is the inverse-image
spelling of the comparison across an open immersion, and the two spellings of a global operator on
`Z` have the same order.

## Main definitions

* `AlgebraicGeometry.globalDiffOpEquivRestrictPullback`: the differential operators of order at
  most `k` between the restrictions of two modules along an open immersion are those between the
  inverse images.
* `AlgebraicGeometry.diffOpEquivGlobalDiffOpPullback`: the differential operators of order at most
  `k` on `W/Y` defined over the opens contained in the image of an open immersion are the
  differential operators of order at most `k` on `Z/Y` between the inverse images.

## Main results

* `AlgebraicGeometry.isGlobalDiffOpOfOrder_globalOpCongr`: conjugating a global operator by
  isomorphisms of the two module sheaves on a scheme preserves the order of a differential
  operator, in both directions.
* `AlgebraicGeometry.isDiffOpOfOrder_restrict_iff_pullback` and
  `AlgebraicGeometry.isGlobalDiffOpOfOrder_restrict_iff_pullback`: an operator on the restrictions
  is a differential operator of order at most `k` exactly when the corresponding operator on the
  inverse images is.
* `AlgebraicGeometry.isDiffOpOfOrder_iff_isGlobalDiffOpOfOrder_pullback`: the order predicates
  across an open immersion correspond, in the inverse-image spelling.

## Implementation notes

Nothing about the order predicate is proved again: conjugation by an isomorphism of module sheaves
is composition on either side with a morphism of module sheaves, which is a differential operator
of order zero, so the general transport `DiffOp.isDiffOpOfOrder_congrIso` applies. The comparison
for the inverse image is then the composite of the comparison for the restriction with that
conjugation, matching the way `AlgebraicGeometry.rawOpEquivGlobalOpPullback` is built from
`AlgebraicGeometry.rawOpEquivGlobalOpRestrict`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Scheme

/-- **Global differential operators across isomorphisms of the modules.** Conjugating a global
operator on local sections by isomorphisms of the source and target module sheaves on a scheme
preserves the order of a differential operator, in both directions. -/
theorem isGlobalDiffOpOfOrder_globalOpCongr {X : Scheme.{u}} {O : TopCat.Sheaf RingCat.{u} X}
    (φ : O ⟶ X.ringCatSheaf) (k : ℕ) {M M' N N' : X.Modules} (eM : M ≅ M') (eN : N ≅ N')
    (D : DiffOp.GlobalOp M N) :
    DiffOp.IsGlobalDiffOpOfOrder φ k (globalOpCongr eM eN D) ↔
      DiffOp.IsGlobalDiffOpOfOrder φ k D :=
  DiffOp.isGlobalDiffOpOfOrder_postcomp_precomp_iff φ k eM eN D

/-- The differential operators of order at most `k` between two module sheaves on a scheme are the
differential operators of order at most `k` between any pair of isomorphic module sheaves. -/
noncomputable def globalDiffOpEquivGlobalOpCongr {X : Scheme.{u}}
    {O : TopCat.Sheaf RingCat.{u} X} (φ : O ⟶ X.ringCatSheaf) (k : ℕ) {M M' N N' : X.Modules}
    (eM : M ≅ M') (eN : N ≅ N') :
    {D : DiffOp.GlobalOp M N // DiffOp.IsGlobalDiffOpOfOrder φ k D} ≃
      {E : DiffOp.GlobalOp M' N' // DiffOp.IsGlobalDiffOpOfOrder φ k E} :=
  Equiv.subtypeEquiv (globalOpCongr eM eN) fun D ↦
    (isGlobalDiffOpOfOrder_globalOpCongr φ k eM eN D).symm

section OpenImmersion

variable {Z W Y : Scheme.{u}} (j : Z ⟶ W) [IsOpenImmersion j] (p : W ⟶ Y)

/-- **The order of a differential operator over a base open, for the inverse image across an open
immersion.** An operator on the local sections of the restrictions of two modules along an open
immersion `j : Z ⟶ W`, defined over the opens below a base open of `Z`, is a differential operator
of order at most `k` on `Z/Y` exactly when the corresponding operator on the local sections of the
inverse images is. -/
theorem isDiffOpOfOrder_restrict_iff_pullback (M M' : W.Modules) (k : ℕ) (U : Z.Opens)
    (D : DiffOp.RawOp (M.restrict j) (M'.restrict j) U) :
    DiffOp.IsDiffOpOfOrder (j ≫ p).relativeStructureSheafMap k D ↔
      DiffOp.IsDiffOpOfOrder (j ≫ p).relativeStructureSheafMap k
        (DiffOp.RawOp.congrIso ((Scheme.Modules.restrictFunctorIsoPullback j).app M)
          ((Scheme.Modules.restrictFunctorIsoPullback j).app M') D) :=
  (DiffOp.isDiffOpOfOrder_congrIso _ k _ _ D).symm

/-- **The order of a global differential operator, for the inverse image across an open
immersion.** A global operator on the local sections of the restrictions of two modules along an
open immersion `j : Z ⟶ W` is a differential operator of order at most `k` on `Z/Y` exactly when
the corresponding operator on the local sections of the inverse images is. -/
theorem isGlobalDiffOpOfOrder_restrict_iff_pullback (M M' : W.Modules) (k : ℕ)
    (E : DiffOp.GlobalOp (M.restrict j) (M'.restrict j)) :
    DiffOp.IsGlobalDiffOpOfOrder (j ≫ p).relativeStructureSheafMap k E ↔
      DiffOp.IsGlobalDiffOpOfOrder (j ≫ p).relativeStructureSheafMap k
        (globalOpCongr ((Scheme.Modules.restrictFunctorIsoPullback j).app M)
          ((Scheme.Modules.restrictFunctorIsoPullback j).app M') E) :=
  (isGlobalDiffOpOfOrder_globalOpCongr _ k _ _ E).symm

/-- **Differential operators for the inverse image across an open immersion.** The differential
operators of order at most `k` on `Z/Y` between the restrictions of two modules along an open
immersion `j : Z ⟶ W` are the differential operators of order at most `k` on `Z/Y` between the
inverse images of those modules. -/
noncomputable def globalDiffOpEquivRestrictPullback (M M' : W.Modules) (k : ℕ) :
    {E : DiffOp.GlobalOp (M.restrict j) (M'.restrict j) //
        DiffOp.IsGlobalDiffOpOfOrder (j ≫ p).relativeStructureSheafMap k E} ≃
      {E : DiffOp.GlobalOp ((Scheme.Modules.pullback j).obj M)
          ((Scheme.Modules.pullback j).obj M') //
        DiffOp.IsGlobalDiffOpOfOrder (j ≫ p).relativeStructureSheafMap k E} :=
  globalDiffOpEquivGlobalOpCongr (j ≫ p).relativeStructureSheafMap k
    ((Scheme.Modules.restrictFunctorIsoPullback j).app M)
    ((Scheme.Modules.restrictFunctorIsoPullback j).app M')

/-- **The order of a differential operator across an open immersion, for the inverse image.** An
operator on the local sections of modules on `W`, defined over the opens contained in the image of
an open immersion `j : Z ⟶ W`, is a differential operator of order at most `k` on `W/Y` exactly
when the corresponding global operator on the inverse images along `j` is a differential operator
of order at most `k` on `Z/Y`. -/
theorem isDiffOpOfOrder_iff_isGlobalDiffOpOfOrder_pullback (M M' : W.Modules) (k : ℕ)
    (D : DiffOp.RawOp M M' j.opensRange) :
    DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k D ↔
      DiffOp.IsGlobalDiffOpOfOrder (j ≫ p).relativeStructureSheafMap k
        (rawOpEquivGlobalOpPullback j M M' D) :=
  (isDiffOpOfOrder_iff_isGlobalDiffOpOfOrder_restrict j p M M' k D).trans
    (isGlobalDiffOpOfOrder_restrict_iff_pullback j p M M' k _)

/-- **Differential operators across an open immersion, for the inverse image.** The differential
operators of order at most `k` on `W/Y` between modules on `W`, defined over the opens contained in
the image of an open immersion `j : Z ⟶ W`, are the differential operators of order at most `k` on
`Z/Y` between the inverse images of those modules along `j`. -/
noncomputable def diffOpEquivGlobalDiffOpPullback (M M' : W.Modules) (k : ℕ) :
    {D : DiffOp.RawOp M M' j.opensRange //
        DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k D} ≃
      {E : DiffOp.GlobalOp ((Scheme.Modules.pullback j).obj M)
          ((Scheme.Modules.pullback j).obj M') //
        DiffOp.IsGlobalDiffOpOfOrder (j ≫ p).relativeStructureSheafMap k E} :=
  Equiv.subtypeEquiv (rawOpEquivGlobalOpPullback j M M')
    (isDiffOpOfOrder_iff_isGlobalDiffOpOfOrder_pullback j p M M' k)

/-- The differential operator on the inverse images corresponding to one on `W/Y` is the value of
the latter at the image of the open, conjugated by the comparison of the restriction with the
inverse image. -/
theorem diffOpEquivGlobalDiffOpPullback_coe_apply (M M' : W.Modules) (k : ℕ)
    (D : {D : DiffOp.RawOp M M' j.opensRange //
      DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k D}) (V : Z.Opens)
    (x : Γ((Scheme.Modules.pullback j).obj M, V)) :
    (diffOpEquivGlobalDiffOpPullback j p M M' k D).1 (op V) x =
      (((Scheme.Modules.restrictFunctorIsoPullback j).app M').hom.app V).hom
        (D.1 (imageOver j V)
          ((((Scheme.Modules.restrictFunctorIsoPullback j).app M).inv.app V).hom x)) := rfl

end OpenImmersion

end AlgebraicGeometry

end
