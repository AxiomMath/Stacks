module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.Homology.Perfect.CompactObjectAnyModel

/-!
# Compact and perfect objects of `D_QCoh(𝒪_X)` on an affine scheme, at any chosen model

Let `R` be a ring and let `K` be an object of `D_QCoh(𝒪_{Spec R})`. Then `K` is a compact object
of `D_QCoh(𝒪_{Spec R})` if and only if `K` is a perfect object of `D(𝒪_{Spec R})`. This is the
affine case of [Stacks, Tag 09M1], stated at an arbitrary chosen model of the two derived
categories rather than at `CategoryTheory.HasDerivedCategory.standard`.

## Main results

* `AlgebraicGeometry.isCompactObject_iff_isPerfect_spec_of_model` — **the affine case of
  [Stacks, Tag 09M1] at an arbitrary chosen derived category.**

## Implementation notes

**Why this is not in `CompactAndPerfect.lean`.** The affine case of Tag 09M1 is already proved
there, as `AlgebraicGeometry.isCompactObject_iff_isPerfect_spec`, and in both directions. But that
file carries `attribute [local instance 10000] HasDerivedCategory.standard` at *file* scope — the
attribute is outside every `namespace` and `section` of the file, so its scope is the whole file
and a declaration added anywhere in it is captured. A statement at another model therefore cannot
be added beside it, and this module exists for that reason alone.

The distinction is not cosmetic. At `HasDerivedCategory.standard` the morphisms of
`D_QCoh(𝒪_X)` live in `Type (u + 1)`, and the direct sums indexed by its own morphism universe
that [Derived Categories, Tag 09SR] asks for do not exist there; the compact-generation results of
this chapter are therefore stated at the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, and the affine case as proved in
`CompactAndPerfect.lean` is unusable at that model. The direction *perfect ⟹ compact* is the one
those results need, and it is exactly the direction that Tag 09M1 does not have on a general
quasi-compact quasi-separated scheme.

**The route.** Three inputs, each already model-generic, compose:
`AlgebraicGeometry.derivedTilde_isEquivalence` ([Stacks, Tag 06Z0]) writes `K = M̃` for an object
`M` of `D(R)`; `StacksDraft.Perfect.AnyModel.isPerfect_iff_isCompactObject_max`
([Stacks, Tag 07LT]) identifies the perfect and the compact objects of `D(R)`; and
`AlgebraicGeometry.isPerfect_tilde_iff_of_model` ([Stacks, Tag 08EB]) carries perfectness across
derived sheafification. Compactness itself crosses the equivalence by
`CategoryTheory.isCompactObject_iff_isCompactObject_obj`, which holds for an additive equivalence
at a *fixed* index universe, so the index universe `u` of the conclusion is unrelated to the
morphism universe of either model.

The index universe is `u` and not the morphism universe of `D_QCoh(𝒪_{Spec R})` on purpose: that
is what `CategoryTheory.Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated` and
[Derived Categories, Tag 09SR] ask for, and at a locally small model the two coincide.

## References

* [The Stacks Project, Proposition 36.17.1 (09M1)](https://stacks.math.columbia.edu/tag/09M1)
* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [The Stacks Project, Lemma 36.10.7 (08EB)](https://stacks.math.columbia.edu/tag/08EB)
* [The Stacks Project, Proposition 15.80.3 (07LT)](https://stacks.math.columbia.edu/tag/07LT)
* [The Stacks Project, Proposition 13.37.6 (09SR)](https://stacks.math.columbia.edu/tag/09SR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe w₁ w₂ u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u}) [hS : HasDerivedCategory.{w₁} (Spec R).Modules]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]

/-- Derived sheafification, read as taking values in the quasi-coherent derived category, is
additive: it is so after the faithful inclusion of the full subcategory, where it is the derived
functor of the exact functor `M ↦ M̃`. -/
instance derivedTilde_additive : (derivedTilde R).Additive :=
  have _h : (derivedTilde R ⋙ ObjectProperty.ι
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf))).Additive :=
    inferInstanceAs ((tilde.functor R).mapDerivedCategory).Additive
  Functor.additive_of_comp_faithful (derivedTilde R)
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)))

/-- **The affine case of [Stacks, Tag 09M1], at an arbitrary chosen derived category.** Let `R` be
a ring and let `K` be an object of `D_QCoh(𝒪_{Spec R})`, for any chosen model of `D(R)` and any
chosen model of `D(𝒪_{Spec R})`. Then `K` is a compact object of `D_QCoh(𝒪_{Spec R})`, with the
direct sums tested over index types in `Type u`, if and only if `K` is a perfect object of
`D(𝒪_{Spec R})`.

Writing `K = M̃` for an object `M` of `D(R)`, which is possible because `M ↦ M̃` is an equivalence
([Stacks, Tag 06Z0]), compactness of `K` is compactness of `M` because compactness at a fixed
index universe crosses an additive equivalence, compactness of `M` is perfectness of `M` by
[Stacks, Tag 07LT], and perfectness of `M` is perfectness of `M̃` by [Stacks, Tag 08EB].

This is `AlgebraicGeometry.isCompactObject_iff_isPerfect_spec` with the pin on the standard model
removed; see the implementation notes for why it cannot be added beside it. -/
@[stacks 09M1 "the affine case, both directions, at an arbitrary chosen derived category -- in \
particular at the locally small AlgebraicGeometry.Scheme.Modules.hasDerivedCategory, at which the \
companion AlgebraicGeometry.isCompactObject_iff_isPerfect_spec says nothing. The global case is \
not covered here"]
theorem isCompactObject_iff_isPerfect_spec_of_model
    (K : Stacks.Duality.quasiCoherentDerivedCategory (Spec R)) :
    IsCompactObject.{u} K ↔
      @Stacks.Cohomology.PerfectComplexes.IsPerfect (Spec R).toRingedSpace hS K.obj := by
  let M := (derivedTilde R).asEquivalence.inverse.obj K
  have hKe : (derivedTilde R).obj M ≅ K := (derivedTilde R).asEquivalence.counitIso.app K
  have hKobj : (tilde.functor R).mapDerivedCategory.obj M ≅ K.obj :=
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf))).mapIso hKe
  exact Iff.trans ⟨isCompactObject_of_iso hKe, isCompactObject_of_iso hKe.symm⟩
    ((isCompactObject_iff_isCompactObject_obj (derivedTilde R) M).symm.trans
      ((StacksDraft.Perfect.AnyModel.isPerfect_iff_isCompactObject_max.{u, u} M).symm.trans
        ((isPerfect_tilde_iff_of_model M).symm.trans
          ⟨fun h => @Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, w₁}
              (Spec R).toRingedSpace hS _ _ hKobj h,
            fun h => @Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, w₁}
              (Spec R).toRingedSpace hS _ _ hKobj.symm h⟩)))

end AlgebraicGeometry

end
