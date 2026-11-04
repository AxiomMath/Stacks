module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent

/-!
# An invertible module on a representable algebraic space comes from the underlying scheme

Let `U` be an object of the big fppf site over `S` and let `N` be an invertible `𝒪`-module on
the small étale site of the representable algebraic space `yoneda.obj U`.  Then `N` is the
image, under the comparison
`AlgebraicGeometry.Space.representedQuasicoherentSheavesEquivalence`, of a quasi-coherent
`AlgebraicGeometry.Scheme.Modules` on the scheme underlying `U`.

Two results are composed:
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isInvertible`, which is Stacks 0B8Q on the
small étale site of an algebraic space followed by Stacks 03DL, and
`AlgebraicGeometry.Space.representedQuasicoherentSheavesEquivalence`, which is Descent,
Proposition 03DX (2) at `τ = étale` for a scheme
(`AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`, unconditional by
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`) composed with the
identification of the small étale site of `yoneda.obj U` with that of the scheme underlying `U`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isInvertibleModule`: an invertible
  `𝒪`-module on an algebraic space is quasi-coherent, with invertibility in the spelling
  `AlgebraicGeometry.Space.IsInvertibleModule` that the Picard-group files use.
* `AlgebraicGeometry.Space.exists_representedQcoh_iso_of_isInvertibleModule`: **an invertible
  module on the small étale site of a representable algebraic space is the comparison image of
  a quasi-coherent module on the underlying scheme.**

## Implementation notes

Triviality of an invertible module on the small étale site of the spectrum of a local ring is
proved, as
`AlgebraicGeometry.Space.nonempty_iso_unit_of_isInvertibleModule_of_forall_eq_top`
(`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedInvertibleTrivial.lean`), and it is what
discharges the choice of a generator in Stacks 0EPQ,
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_of_isTrivialAtCodimensionZeroPoints`
(`StacksFrontier/AlgebraicGeometry/Spaces/RegularMeromorphicSectionExistence.lean`).

**That proof does not go through this file**, and the two earlier readings of what it would
need, both recorded here, were wrong.  The first said the statement needed a comparison between
modules on the small étale site and quasi-coherent modules on the scheme, said to be unavailable
even for an affine scheme; the comparison is the equivalence used below.  The second said what
remained was the passage of *invertibility* across that comparison: the comparison functor is
`AlgebraicGeometry.SmallEtale.associatedModule`, the pullback of modules along the morphism of
ringed sites `(T_étale, 𝒪) → (T_Zar, 𝒪_T)`, and the tensor comparison of Stacks 03EL that would
carry a tensor inverse across it, `Stacks.SheafOfModules.pullbackTensorIso`, is stated for the
pullback of a `Stacks.Sheaves.RingedToposModules.RingedToposHom`, which that comparison is not
stated as — it is the `AlgebraicGeometry.RingedToposSiteHom`
`AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRingedToposHom.lean`), and
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` is defined only for two ringed topoi whose
object, morphism and section universes all agree, which the small Zariski and small étale sites
of a scheme do not.  None of that is needed: the proof never
carries a tensor inverse across the comparison.  Invertibility is used only at a geometric point,
where `AlgebraicGeometry.Space.geometricModuleStalkTensorIso` is Stacks 03EL; the resulting
freeness of rank one descends to the Zariski stalk of the chart along Stacks 05VP by
`Module.nonempty_linearEquiv_of_tensorProduct_of_faithfullyFlat`, and what crosses the
Zariski–étale comparison afterwards is an isomorphism of quasi-coherent modules, which
`AlgebraicGeometry.SmallEtale.nonempty_iso_of_iso_restrictModule` reflects.

So the chain this file's notes used to describe — full faithfulness on quasi-coherent modules
plus `Stacks.PicardUFD.isTrivial_of_isInvertible_spec` after a tensor comparison — remains one
possible route and is not the one taken.  The two results below stand on their own.

No `stacks` attribute is attached: neither statement is a clause of a tag, both being
compositions of results that carry their own.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An invertible `𝒪_Z`-module on the small étale site of an algebraic space `Z` is
quasi-coherent.  This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isInvertible` with
invertibility in the spelling `AlgebraicGeometry.Space.IsInvertibleModule`, the one
`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctor.lean` states the Picard group with. -/
theorem isQuasicoherentOnSite_of_isInvertibleModule (Z : AlgebraicSpaces B S hS)
    (N : Modules.{u, u} B S hS Z.1 Z.2) (hN : IsInvertibleModule Z N) :
    N.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isInvertible B S hS Z N hN.toAlgebraicGeometry

/-- **An invertible module on the small étale site of a representable algebraic space comes from
the underlying scheme.**  It is quasi-coherent, hence is the image of a quasi-coherent
`AlgebraicGeometry.Scheme.Modules` on the scheme underlying `U` under the comparison
`AlgebraicGeometry.Space.representedQuasicoherentSheavesEquivalence`. -/
theorem exists_representedQcoh_iso_of_isInvertibleModule (U : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : IsInvertibleModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ N) :
    ∃ M : (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory,
      Nonempty
        (((representedQuasicoherentSheavesEquivalence B S hS U).functor.obj M).obj ≅ N) := by
  have hqc : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertibleModule
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ N hN
  exact ⟨(representedQuasicoherentSheavesEquivalence B S hS U).inverse.obj ⟨N, hqc⟩,
    ⟨(ObjectProperty.ι _).mapIso
      ((representedQuasicoherentSheavesEquivalence B S hS U).counitIso.app ⟨N, hqc⟩)⟩⟩

end AlgebraicGeometry.Space

end
