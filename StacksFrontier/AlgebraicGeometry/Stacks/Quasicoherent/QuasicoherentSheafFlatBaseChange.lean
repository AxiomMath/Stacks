module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineCriterion

/-!
# Quasi-coherent modules lie in `LQCoh^fbc` (the flat base change half of Stacks 06WK)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `F` a quasi-coherent module on
its fppf site (**Stacks 06WG**). This file proves that `F` has the flat base change property of
**Stacks 0762**, in the sheaf-level reading
`AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty` (see
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty` for why the
presheaf-level reading of the library is false for quasi-coherent modules). Together with local
quasi-coherence, `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isQuasicoherentOnSite`, this
is the containment `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` of Stacks, Section 0GQG, the forward direction of
clause (1) of **Stacks 06WK**, which **Stacks 0778** uses to form its inclusion functor.

A quasi-coherent module is cartesian along every arrow between objects lying over affine schemes,
`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`, so the
affine criterion
`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange` applies.

## Main results

* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isQuasicoherentOnSite`: a
  quasi-coherent module has the flat base change property of Stacks 0762.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithSheafFlatBaseChange_of_isQuasicoherentOnSite`:
  a quasi-coherent module lies in `LQCoh^fbc(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasSheafFlatBaseChangeProperty_quasicoherentInclusion`
  and `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohSheafFbcFppfModules_quasicoherentInclusion`:
  the same for the objects of `QCoh(𝒪_𝒳)` of an algebraic stack, at module universe `u`.

## Implementation notes

The statements for algebraic stacks are spelled with the underlying full subcategory
`FibredSite.quasicoherentModules` and its inclusion rather than with
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules` and
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentInclusion`, which are abbreviations of
exactly these. This keeps the module below the one defining those abbreviations, so that it can
be imported there; for a consumer the two spellings are interchangeable.

## References

* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **A quasi-coherent module has the flat base change property** (Stacks 06WK, the flat base
change half of the forward direction of clause (1)): a quasi-coherent module on the fppf site of
`𝒳` (**Stacks 06WG**), read on the étale site, has the flat base change property of
**Stacks 0762**. -/
theorem hasSheafFlatBaseChangeProperty_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) :
    HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) M.val :=
  hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange B E h S hS p hp M.val
    (isLocallyQuasicoherent_of_isQuasicoherentOnSite B E h S hS p hp M hM)
    (fun φ hx hy _ => FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite M hM φ hx hy)

/-- **`QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)`** (Stacks, Section 0GQG; Stacks 06WK, forward direction of
clause (1)): a quasi-coherent module on the fppf site of `𝒳`, read on the étale site, is locally
quasi-coherent and has the flat base change property of **Stacks 0762**. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp M.val :=
  ⟨isLocallyQuasicoherent_of_isQuasicoherentOnSite B E h S hS p hp M hM,
    hasSheafFlatBaseChangeProperty_of_isQuasicoherentOnSite B E h S hS p hp M hM⟩

namespace AlgebraicStacks

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The objects of `QCoh(𝒪_𝒳)` of an algebraic stack, at module universe `u`, have the flat base
change property of **Stacks 0762**. -/
theorem hasSheafFlatBaseChangeProperty_quasicoherentInclusion
    (M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    HasSheafFlatBaseChangeProperty B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B)
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι.obj M).val :=
  hasSheafFlatBaseChangeProperty_of_isQuasicoherentOnSite B E h S hS _ _ M.obj M.property

/-- **`QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)`** for an algebraic stack, at module universe `u`: every object
of `QCoh(𝒪_𝒳)` lies in `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`. -/
theorem lqcohSheafFbcFppfModules_quasicoherentInclusion
    (M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι.obj M) :=
  isLocallyQuasicoherentWithSheafFlatBaseChange_of_isQuasicoherentOnSite B E h S hS _ _
    M.obj M.property

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
