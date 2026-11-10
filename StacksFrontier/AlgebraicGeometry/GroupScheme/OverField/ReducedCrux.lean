/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ReducedOfStalkUnit
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.TranslatedRationalQuotient
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ReductionSubgroupGlue
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AffineStabilizer
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.FibresInStabilizer
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.TranslatedSmoothModel
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.RationalQuotientModel

/-!
# The unit of a group scheme in characteristic zero: assembling Perrin's argument

Let `H` be a group scheme over an algebraically closed field `Ω` of characteristic zero which is
irreducible, Jacobson, and whose closed points are `Ω`-rational, and let `Γ ⊆ H` be its
reduction. This file assembles the pieces of Perrin's argument into the statement that the local
ring of `H` at the unit is reduced:

* a smooth affine model `π : W ⟶ X` of a left-invariant finitely generated subfield of the
  function field of `Γ`, flat and quasi-compact on an open `W` of `Γ`, whose fibres lie in left
  translates of an affine closed subgroup scheme `Z ⊆ Γ` of finite presentation over `H`, is
  translated by a rational point of `W` to a neighbourhood of the unit
  (`AlgebraicGeometry.translatedQuotient`) and extended across the nil-thickening `Γ ⊆ H`;
* the lifting lemma then makes `Γ → H` of finite presentation near the unit, and the local Cartier
  theorem makes the local ring at the unit reduced
  (`AlgebraicGeometry.isReduced_stalk_identity_of_lifting`).

## Main results

* `AlgebraicGeometry.isReduced_stalk_identity_of_smoothModel`.
* `AlgebraicGeometry.isReduced_stalk_identity_of_irreducible_of_jacobson`: the hypothesis of
  `AlgebraicGeometry.isReduced_of_forall_isReduced_stalk_unit_of_irreducible`, proved.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

open CategoryTheory.MonObj CategoryTheory.GrpObj in
/-- **The end of Perrin's argument, from a smooth model.** Let `H` be a group scheme over a field
`k` of characteristic zero, `L ⊆ H` its reduction (a reduced closed subgroup scheme with the same
underlying space), `Z ⊆ L` a closed subscheme with `Z → H` locally of finite presentation, and
`π : W ⟶ X` a flat quasi-compact `k`-morphism from an open `W` of `L` to a smooth affine
`k`-scheme whose fibres lie in left translates of `Z`. If `W` contains a rational point `g`, the
local ring of `H` at the unit is reduced: translating by `g` moves `π` to a neighbourhood of the
unit, where it extends across the nil-thickening `L ⊆ H` (`X` is smooth and affine), and the
lifting lemma applies. -/
theorem isReduced_stalk_identity_of_smoothModel (k : Type u) [Field k] [CharZero k]
    (H : Grp (Over (Spec (.of k)))) (L : ClosedSubgroupScheme H) [Surjective L.ι.hom.hom.left]
    [IsReduced L.carrier.X.left] {Z : Scheme.{u}} (iZ : Z ⟶ L.carrier.X.left)
    [LocallyOfFinitePresentation (iZ ≫ L.ι.hom.hom.left)]
    (W : L.carrier.X.left.Opens) (X : Over (Spec (.of k))) [IsAffine X.left] [Smooth X.hom]
    (π : W.toScheme ⟶ X.left) (hπ : π ≫ X.hom = W.ι ≫ L.carrier.X.hom) [QuasiCompact π] [Flat π]
    (h : ∀ (T : Over (Spec (.of k))) (x y : T ⟶ L.carrier.X) (x' y' : T.left ⟶ W.toScheme),
      x' ≫ W.ι = x.left → y' ≫ W.ι = y.left → x' ≫ π = y' ≫ π →
      letI := Hom.group (X := T) (G := L.carrier.X)
      ∃ z : T.left ⟶ Z, z ≫ iZ = (x⁻¹ * y).left)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ L.carrier.X) (p : (𝟙_ (Over (Spec (.of k)))).left)
    (hg : g.left p ∈ W) :
    _root_.IsReduced (H.X.left.presheaf.stalk (identityPoint k H)) := by
  let Γ := L.carrier.X
  let i := L.ι.hom.hom.left
  have : IsClosedImmersion i := L.isClosedImmersion
  let W₁ := translatedOpen Γ g W
  let π₁ := translatedQuotient Γ g W π
  have hπ₁ : π₁ ≫ X.hom = W₁.ι ≫ Γ.hom := translatedQuotient_over Γ g W X π hπ
  have : QuasiCompact π₁ := by
    change QuasiCompact ((leftTranslation Γ g).left ∣_ W ≫ π)
    infer_instance
  have heW₁ : identityPoint k L.carrier ∈ W₁ := by
    convert unit_mem_translatedOpen Γ g W p hg using 2
    exact Subsingleton.elim (α := Spec (.of k)) _ _
  obtain ⟨U, hU, heU, hUW⟩ := exists_isAffineOpen_preimage_le i W₁ heW₁
  have heU' : identityPoint k H ∈ U := by
    rw [show identityPoint k H = i (identityPoint k L.carrier) from
      (closedSubgroupScheme_ι_unit L _).symm]
    exact heU
  obtain ⟨π', hπ'k, hπ'⟩ :=
    exists_extend_of_closedSubgroupScheme k H L W₁ X π₁ hπ₁ U hU hUW
  exact isReduced_stalk_identity_of_lifting k H L iZ W₁ X π₁ hπ₁ U hUW π' hπ'k hπ'
    (translatedQuotient_fibre Γ g W X.left π
      (fun T z => ∃ z' : T.left ⟶ Z, z' ≫ iZ = z.left) h) heU'

/-- **Perrin's theorem at the unit.** Let `H` be a group scheme over an algebraically closed field
`Ω` of characteristic zero which is irreducible and Jacobson, and whose closed points are
`Ω`-rational. Then the local ring of `H` at the unit is reduced. -/
theorem isReduced_stalk_identity_of_irreducible_of_jacobson (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [CharZero Ω] (H : Grp (Over (Spec (.of Ω)))) [IrreducibleSpace H.X.left]
    [JacobsonSpace H.X.left]
    (hrat : ∀ x ∈ closedPoints H.X.left, ∃ p : 𝟙_ (Over (Spec (.of Ω))) ⟶ H.X,
      p.left (basePoint Ω) = x) :
    _root_.IsReduced (H.X.left.presheaf.stalk (identityPoint Ω H)) := by
  obtain ⟨L, hsurj, hred⟩ := exists_reduction_closedSubgroupScheme H
  let Γ := L.carrier.X
  let i := L.ι.hom.hom.left
  have : IsClosedImmersion i := L.isClosedImmersion
  have : IrreducibleSpace Γ.left := irreducibleSpace_of_isClosedImmersion_of_surjective i
  have : IsIntegral Γ.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : GeometricallyIrreducible Γ.hom := geometricallyIrreducible_of_irreducibleSpace Γ
  obtain ⟨Z, iZ, _, _, _, -, hZe⟩ := exists_affineStabilizer_lift Ω H L
  obtain ⟨U₀, hU₀, he₀, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    Γ.left.isBasis_affineOpens) (show identityPoint Ω L.carrier ∈ (⊤ : Γ.left.Opens) from trivial)
  have hne₀ : (U₀ : Set Γ.left).Nonempty := ⟨_, he₀⟩
  obtain ⟨s, hs⟩ := exists_finset_rightStabilises_lift hU₀
    (zeroDivisors_isNilpotent_tensor_of_charZero Ω L.carrier U₀ hU₀) hne₀ iZ hZe
  obtain ⟨W, X, _, _, π, hπ, _, _, hWne, hfib⟩ :=
    exists_flat_smooth_model_rightStabilises Γ hU₀ hne₀ s
  obtain ⟨g, hg⟩ := exists_rationalPoint_mem_of_surjective H hrat L W hWne
  exact isReduced_stalk_identity_of_smoothModel Ω H L iZ W X π hπ
    (fun T x y x' y' hx hy hxy => hs T _ (hfib T x y x' y' hx hy hxy)) g (basePoint Ω) hg

end AlgebraicGeometry

end

