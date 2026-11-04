module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeBranchResidues
public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationStalk

/-!
# The residue at a point of a fibre, on the stalk of a direct image

Let `ν : Y ⟶ X` be a morphism of schemes over a field `k`, let `y` be a closed point of `Y` and
let `x = ν(y)`. Evaluation at `y` of a local section of `𝒪_Y` defined near the fibre makes sense
on the stalk `(ν_* 𝒪_Y)_x`: the germ at `x` of a section `s` over `ν ⁻¹ᵁ U` is sent to the residue
of the germ of `s` at `y`. When `Y` is locally of finite type over an algebraically closed `k` the
residue field at the closed point `y` is `k` itself, so this evaluation is a `k`-algebra map
`(ν_* 𝒪_Y)_x →ₐ[k] k`, and its kernel is cut out geometrically: a germ is killed exactly when
some representative of it vanishes at `y`.

## Main results

* `Stacks.Curves.exists_algHom_apply_germ_eq_zero_iff_notMem_basicOpen` — **the residue at a
  closed point of `Y` above `x`, as a `k`-algebra map on the stalk of `ν_* 𝒪_Y` at `x`**, together
  with the description of its vanishing locus through the non-vanishing loci `Y.basicOpen s`.

## Implementation notes

The map is the composite of three: the comparison map of stalks
`TopCat.Presheaf.stalkPushforward` from `(ν_* 𝒪_Y)_{ν(y)}` to `𝒪_{Y, y}`, whose defining property
`TopCat.Presheaf.stalkPushforward_germ` is that it takes the germ at `ν(y)` of a section over
`ν ⁻¹ᵁ U` to its germ at `y`; the residue map of the local ring `𝒪_{Y, y}`; and the
identification of the residue field with `k`, which is Zariski's lemma in the form
`Stacks.Curves.nonempty_residueField_stalk_algEquiv_of_isClosed`.

That the composite is a map of `k`-algebras for the structure
`Stacks.Curves.directImageStalkFieldAlgebra` — the germ at `x` of the pullback to `Y` of a global
section of the base, taken along `ν` and then along the structure morphism of `X` — needs the two
routes from `k` to `𝒪_{Y, y}` to agree, which is exactly the compatibility
`ν ≫ hX = (Y ↘ Spec k)` of the structure morphisms and is therefore assumed. Given it, the two
germs agree by `AlgebraicGeometry.Scheme.Hom.comp_app`, and no transport along the compatibility
is needed in the term: `Scheme.Hom.appTop` is stated with the open `⊤` on both sides, so the
structure morphism may be abstracted out of the germ and the compatibility applied with
`congrArg`.

The vanishing condition is read off at the level of the local ring: the residue of a germ is zero
exactly when the germ lies in the maximal ideal, that is when it is not a unit, which by
`AlgebraicGeometry.Scheme.mem_basicOpen` is exactly that `y` lies outside the non-vanishing locus
of the section. Since `ν(y) = x` lies in `U`, the point `y` lies in `ν ⁻¹ᵁ U`, so the germ at `y`
of a section over `ν ⁻¹ᵁ U` is defined.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry IsLocalRing
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

/-- **The residue at a closed point of `Y` above `x`, as a `k`-algebra map on the stalk of
`ν_* 𝒪_Y` at `x`.** Let `ν : Y ⟶ X` be a morphism of schemes over an algebraically closed field
`k` with `Y` locally of finite type over `k`, let `y` be a closed point of `Y` and let
`x = ν(y)`. Then the stalk `(ν_* 𝒪_Y)_x` carries a `k`-algebra map to `k` — evaluation at `y` —
whose vanishing on the germ of a section `s` over `ν ⁻¹ᵁ U` says precisely that `s` vanishes at
`y`.

This is the residue at one of the points of `Y` above `x`; for the normalization of a nodal curve
the two such maps are the two branch residues, and this is the hypothesis on `ε` that
`Stacks.Curves.fixes_stalkDerivation_of_fixes` consumes in order to turn a vector field fixing
`y` into a derivation of `(ν_* 𝒪_Y)_x` fixing the `k`-point that `y` cuts out. -/
public theorem exists_algHom_apply_germ_eq_zero_iff_notMem_basicOpen
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (hX : X ⟶ Spec (.of k))
    (ν : Y ⟶ X) [Y.Over (Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    (hcomp : ν ≫ hX = (Y ↘ Spec (.of k)))
    (y : Y) (hy : IsClosed ({y} : Set Y)) (x : X) (hxy : ν.base y = x) :
    letI := directImageStalkFieldAlgebra ν hX x
    ∃ ε : ((ν.base _* Y.presheaf).stalk x) →ₐ[k] k,
      ∀ (U : X.Opens) (hxU : x ∈ U) (s : Γ(Y, ν ⁻¹ᵁ U)),
        ε ((ν.base _* Y.presheaf).germ U x hxU s) = 0 ↔ y ∉ Y.basicOpen s := by
  subst hxy
  let := directImageStalkFieldAlgebra ν hX (ν.base y)
  let : Algebra k (Y.presheaf.stalk y) := (fieldToStalk (Y ↘ Spec (.of k)) y).hom.toAlgebra
  obtain ⟨eκ⟩ := nonempty_residueField_stalk_algEquiv_of_isClosed k Y y hy
  have hφ : ∀ (U : X.Opens) (hxU : ν.base y ∈ U) (s : Γ(Y, ν ⁻¹ᵁ U)),
      (TopCat.Presheaf.stalkPushforward CommRingCat.{u} ν.base Y.presheaf y).hom
          ((ν.base _* Y.presheaf).germ U (ν.base y) hxU s) =
        Y.presheaf.germ (ν ⁻¹ᵁ U) y hxU s := by
    intro U hxU s
    exact TopCat.Presheaf.stalkPushforward_germ_apply CommRingCat.{u} ν.base Y.presheaf U y hxU s
  refine ⟨AlgHom.mk ((eκ : ResidueField (Y.presheaf.stalk y) →+* k).comp
      ((residue (Y.presheaf.stalk y)).comp
        (TopCat.Presheaf.stalkPushforward CommRingCat.{u} ν.base Y.presheaf y).hom)) ?_,
    fun U hxU s => ?_⟩
  · intro c
    show eκ (residue (Y.presheaf.stalk y)
      ((TopCat.Presheaf.stalkPushforward CommRingCat.{u} ν.base Y.presheaf y).hom
        (algebraMap k ((ν.base _* Y.presheaf).stalk (ν.base y)) c))) = algebraMap k k c
    have h : (TopCat.Presheaf.stalkPushforward CommRingCat.{u} ν.base Y.presheaf y).hom
        (algebraMap k ((ν.base _* Y.presheaf).stalk (ν.base y)) c) =
        algebraMap k (Y.presheaf.stalk y) c :=
      (hφ (hX ⁻¹ᵁ ⊤) trivial _).trans
        (congrArg (fun g : Y ⟶ Spec (.of k) => Y.presheaf.germ ⊤ y trivial
          (g.appTop ((Scheme.ΓSpecIso (.of k)).inv.hom c))) hcomp)
    rw [h, ← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact eκ.commutes c
  · show eκ (residue (Y.presheaf.stalk y)
      ((TopCat.Presheaf.stalkPushforward CommRingCat.{u} ν.base Y.presheaf y).hom
        ((ν.base _* Y.presheaf).germ U (ν.base y) hxU s))) = 0 ↔ y ∉ Y.basicOpen s
    rw [hφ U hxU s, map_eq_zero_iff eκ eκ.injective, residue_eq_zero_iff, mem_maximalIdeal,
      mem_nonunits_iff, Scheme.mem_basicOpen Y s y hxU]

end Stacks.Curves

end
