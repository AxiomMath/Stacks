module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.DegreewiseComparison

/-!
# Locality on the base of the degreewise comparison

The assertion of [Stacks, Tag 0GN5] is that a morphism of `𝒪_{S'}`-modules — the degreewise
comparison map of `DegreewiseComparison.lean` — is invertible. Invertibility of a morphism of
sheaves of modules is a local condition, so the assertion may be checked on a covering of `S'`,
and the covering may be taken to consist of affine opens each contained in the inverse image of
an affine open of `S`. This file records both halves of that reduction.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app_iff_stalkwise`:
  **invertibility of the degreewise comparison is a stalkwise condition on `S'`**, hence local
  on `S'` in the strongest sense.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isOpenCover_affinePairs`: **the affine opens of
  `S'` lying over affine opens of `S` cover `S'`.** This is the geometric content of the
  reduction of a condition local on `S'` to a condition on pairs of affine opens
  `V ⊆ g ⁻¹ᵁ U`.

## Implementation notes

Invertibility is read stalkwise through
`AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap`, which is stated over
`SheafOfModules O` for a sheaf of rings `O` on a topological space — the spelling the degreewise
comparison is written in. The alternative formulation, invertibility after restriction to each
member of an open covering
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`), is stated over
`AlgebraicGeometry.Scheme.Modules`; both are consequences of the same stalkwise criterion.

The covering lemma is `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset` applied twice:
once in `S`, to find an affine open `U` around the image of a point, and once in `S'`, to find
an affine open `V` around the point inside `g ⁻¹ᵁ U`. It mentions neither the comparison map nor
any hypothesis on the square, and is the form in which
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_affineBases`
uses the same two applications.

**What is not here.** The passage from the restriction of the degreewise comparison to the
degreewise comparison of the restricted square is not proved. It needs three inputs: that
restriction to an open of `S'` commutes with the two coefficient functors, that it commutes with
`R ⁱ f'_*` (which is
`AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictIsoScheme`), and a pasting
equation expressing the degreewise comparison of a rectangle as a composite — the analogue, for
the degreewise map, of
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeSquare_pasteBase`. The last is the
substantial one: the degreewise comparison is defined through
`CategoryTheory.Functor.rightDerivedDesc`, so a pasting law for it is not a formal consequence of
the mate calculus that supplies the underived one.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 007T](https://stacks.math.columbia.edu/tag/007T)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {S S' X X' : Scheme.{u}}

/-! ### Invertibility is stalkwise on the base -/

/-- **Invertibility of the degreewise comparison of [Stacks, Tag 0GN5] is a stalkwise condition
on `S'`.**  A morphism of sheaves of modules is an isomorphism exactly when it is bijective on
every stalk, so the assertion of the tag at a given `F` and `i` is a condition on the points of
`S'`; in particular it is local on `S'`. -/
theorem isIso_degreewiseComparison_app_iff_stalkwise {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) (i : ℕ)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    IsIso ((degreewiseComparison H G hG i).app F) ↔
      ∀ x : S'.carrier,
        Function.Bijective
          (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing S'.toRingedSpace) x
            ((degreewiseComparison H G hG i).app F)).hom :=
  AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap _

/-! ### The affine opens of `S'` lying over affine opens of `S` cover `S'` -/

/-- The index type of the covering of `S'` by affine opens lying over affine opens of `S`: a
pair of an affine open `U` of `S` and an affine open `V` of `S'` with `V ≤ g ⁻¹ᵁ U`. -/
abbrev AffinePair (g : S' ⟶ S) : Type u :=
  { p : S.Opens × S'.Opens // IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ p.2 ≤ g ⁻¹ᵁ p.1 }

/-- **The affine opens of `S'` lying over affine opens of `S` cover `S'`.**  Every point of `S'`
has an affine open neighbourhood contained in the inverse image of an affine open neighbourhood
of its image in `S`: choose the affine open of `S` first and then shrink inside its inverse
image. This is what reduces a condition local on `S'` to a condition on pairs of affine opens
`V ⊆ g ⁻¹ᵁ U`. -/
theorem isOpenCover_affinePairs (g : S' ⟶ S) :
    IsOpenCover (fun p : AffinePair g => p.1.2) := by
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := S) (x := g.base x)
      (U := ⊤) (by trivial)
  obtain ⟨V, hVaff, hxV, hVle⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := S') (x := x)
      (U := g ⁻¹ᵁ U) hxU
  exact Opens.mem_iSup.2 ⟨⟨(U, V), hU, hVaff, hVle⟩, hxV⟩

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
