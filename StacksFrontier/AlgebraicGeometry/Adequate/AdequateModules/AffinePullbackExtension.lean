module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateSectionExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.QcohPullbackOpenCover
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# Acyclicity of a pullback to a spectrum is acyclicity of an extension of scalars

The last step of [Stacks, Tag 06ZR] compares universal acyclicity of a complex `K` of
quasi-coherent `𝒪_{Spec A}`-modules with a condition over the `A`-algebras. Universal acyclicity
is acyclicity of the pullbacks of `K` in the categories of **all** `𝒪_T`-modules; the condition
over an algebra `C` is acyclicity of a complex of `C`-modules. This module identifies the two for
`T = Spec C`.

The identification rests on two facts about `M ↦ M^~`. It carries the extension of scalars along
`φ : A ⟶ C` to the pullback along `Spec φ` — [Stacks, Tag 01I9],
`AlgebraicGeometry.pullbackTildeIso` — so the complex of `𝒪_{Spec C}`-modules under comparison is
`(C ⊗_A Γ(Spec A, K))^~`. And it is exact and fully faithful, by
`Stacks.AffineTilde.tildeFunctor_preservesHomology` and
`AlgebraicGeometry.tilde.fullyFaithfulFunctor`, so it detects acyclicity, which is
`Stacks.Adequate.plus_acyclic_map_iff`.

## Main definitions

* `Stacks.Adequate.tildeExtendScalarsQcohPullbackIso` — **taking sections over `Spec A`,
  extending scalars along `φ` and taking the associated sheaf is pulling back along `Spec φ`.**

## Main results

* `Stacks.Adequate.plus_subcategoryAcyclic_qcohPullback_spec_iff` — **the pullback of `K` to
  `Spec C` is acyclic exactly when the complex of `C`-modules `C ⊗_A Γ(Spec A, K)` is acyclic.**

## Implementation notes

The comparison is deliberately routed through `AlgebraicGeometry.tilde.functor`, which lands in
**all** `𝒪_{Spec C}`-modules, rather than through the pullback of quasi-coherent modules and the
inclusion of the quasi-coherent modules. The quasi-coherent modules on a scheme carry two paths
to their additive structure — the one a full subcategory inherits, and the one coming from the
abelian structure that a weak Serre subcategory has — and typeclass synthesis, being
reducible-only, does not identify them: a route through `QCoh(𝒪_{Spec C})` leaves
`(SheafOfModules.isQuasicoherent (Spec C).ringCatSheaf).ι.Additive` unsynthesizable. Going
through `tilde.functor` never mentions the quasi-coherent modules over `Spec C`, so the only
additive structures occurring are that of `QCoh(𝒪_{Spec A})`, which the complex `K` fixes, and
those of the module categories.

For the same reason the isomorphism is stated with `Stacks.Adequate.qcohPullback` on the right:
its additivity `Stacks.Adequate.qcohPullback_additive` is stated over an arbitrary additive
structure on `QCoh(𝒪_{Spec A})`, and so applies to whichever one `K` carries.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Adequate

/-- The global sections functor of an affine scheme, read on the quasi-coherent modules, is
additive: it is the inverse of the equivalence `AlgebraicGeometry.tildeEquiv`, hence preserves
binary products. -/
public instance additive_tildeEquiv_inverse (R : CommRingCat.{u}) :
    (tildeEquiv (R := R)).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

variable (A C : CommRingCat.{u}) (φ : A ⟶ C)

/-- **Taking sections over `Spec A`, extending scalars along `φ` and taking the associated sheaf
is pulling back along `Spec φ`.** The middle step is [Stacks, Tag 01I9],
`AlgebraicGeometry.pullbackTildeIso`; the outer ones cancel because the associated sheaf of the
sections of a quasi-coherent module is that module, which is the counit of
`AlgebraicGeometry.tildeEquiv`. -/
public noncomputable def tildeExtendScalarsQcohPullbackIso :
    ((tildeEquiv (R := A)).inverse ⋙ ModuleCat.extendScalars φ.hom) ⋙ tilde.functor C ≅
      qcohPullback (Spec.map φ) :=
  Functor.isoWhiskerLeft (tildeEquiv (R := A)).inverse
      (AlgebraicGeometry.pullbackTildeIso A C φ).symm ≪≫
    Functor.isoWhiskerRight (tildeEquiv (R := A)).counitIso
      ((SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (Spec.map φ)) ≪≫
    Functor.leftUnitor _

/-- **The identification of the two readings of the last step of [Stacks, Tag 06ZR].** The
pullback to `Spec C` of a bounded below complex `K` of quasi-coherent `𝒪_{Spec A}`-modules is
acyclic exactly when the complex of `C`-modules `C ⊗_A Γ(Spec A, K)` is acyclic.

The two complexes of `𝒪_{Spec C}`-modules under comparison are identified by
`Stacks.Adequate.tildeExtendScalarsQcohPullbackIso`, and `M ↦ M^~` detects acyclicity, being
exact — `Stacks.AffineTilde.tildeFunctor_preservesHomology` — and fully faithful,
`AlgebraicGeometry.tilde.fullyFaithfulFunctor`. -/
public theorem plus_subcategoryAcyclic_qcohPullback_spec_iff
    (K : HomotopyCategory.Plus
      (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory) :
    HomotopyCategory.Plus.subcategoryAcyclic (Spec C).Modules
        ((qcohPullback (Spec.map φ)).mapHomotopyCategoryPlus.obj K) ↔
      HomotopyCategory.Plus.subcategoryAcyclic (ModuleCat.{u} ↥C)
        (((tildeEquiv (R := A)).inverse ⋙
          ModuleCat.extendScalars φ.hom).mapHomotopyCategoryPlus.obj K) := by
  let := Stacks.AffineTilde.tildeFunctor_preservesHomology C
  let := (AlgebraicGeometry.tilde.fullyFaithfulFunctor (R := C)).reflectsIsomorphisms
  have e := (Functor.mapHomotopyCategoryPlusCompIso
    (tildeExtendScalarsQcohPullbackIso A C φ)).app K
  refine Iff.trans
    ((HomotopyCategory.Plus.subcategoryAcyclic (Spec C).Modules).prop_iff_of_iso e.symm) ?_
  exact plus_acyclic_map_iff (tilde.functor C) _

end Stacks.Adequate

end
