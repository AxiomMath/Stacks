module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsClauseOneToTwo
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsPerfect
public import StacksFrontier.Homology.DerivedCategory.ModelComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Invertible objects in the derived category of a ringed site

Let `(C, O)` be a ringed site and let `M` be an object of `D(O)`. Stacks 0FPY says that the
following are equivalent:

1. `M` is invertible in `D(O)`;
2. there is a locally finite direct product decomposition `O = ∏ O_n` and for each `n` an
   invertible `O_n`-module `ℋ^n` with `M = ⨁ ℋ^n[-n]` in `D(O)`;

that if they hold `M` is perfect; and that if `(C, O)` is locally ringed they are also equivalent
to

3. for every object `U` of `C` there is a covering `{U_i → U}` and integers `n_i` such that
   `M|_{U_i}` is represented by an invertible `O_{U_i}`-module placed in degree `n_i`.

This file proves the tag, as
`AlgebraicGeometry.RingedSite.InvertibleDerived.isInvertibleObject_tfae`.

## Main results

* `AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfect_of_isInvertibleObject`: an invertible
  object of `D(O)` is perfect, for any model of `D(O)`. This is the step of the source's proof of
  `(1) ⟹ (2)` which appeals to Stacks 0FPV.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.isInvertibleObject_tfae`: **Stacks 0FPY.**

## Implementation notes

`AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfect_of_isInvertibleObject_standard` proves
perfectness when the derived categories of the modules on `C` and on its slices are the standard
ones. Neither invertibility nor perfectness depends on the model: an invertible `M` with inverse
`N` is represented by K-flat complexes `M^•`, `N^•` with `Q(Tot(M^• ⊗ N^•)) ≅ Q(O[0])` and
`Q(Tot(N^• ⊗ M^•)) ≅ Q(O[0])`; these isomorphisms are carried to the standard model along the
comparison equivalence of the two localizations (`StacksDraft.DerivedModel.modelEquiv`,
`StacksDraft.DerivedModel.modelCompQIso`), where they make `Q(M^•)` invertible; and the perfect
complex representing `Q(M^•)` there is carried back the same way.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {X : RingedSite.{u, u, u}} [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An isomorphism between the images of two complexes in one model of the derived category of
an abelian category, carried to another model along the comparison of the two localizations. -/
def qObjIsoOfModel {A : Type*} [Category A] [Abelian A] (h₁ : HasDerivedCategory.{d} A)
    (h₂ : HasDerivedCategory A) {K L : CochainComplex A ℤ}
    (e : (@DerivedCategory.Q A _ _ h₁).obj K ≅ (@DerivedCategory.Q A _ _ h₁).obj L) :
    (@DerivedCategory.Q A _ _ h₂).obj K ≅ (@DerivedCategory.Q A _ _ h₂).obj L :=
  ((StacksDraft.DerivedModel.modelCompQIso h₁ h₂).app K).symm ≪≫
    (StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor.mapIso e ≪≫
      (StacksDraft.DerivedModel.modelCompQIso h₁ h₂).app L

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Two K-flat complexes whose total tensor products, in both orders, are quasi-isomorphic to
`O[0]` have perfect images**, in the standard model of `D(O)`: the images are mutually inverse
objects of `D(O)`, by the two comparisons of Stacks 0FPT, so
`isPerfect_of_isInvertibleObject_standard` applies. -/
theorem exists_isPerfectComplex_of_tensorIsoUnit_standard (Mc Nc : Complexes X.O)
    (hMc : KFlat X.O Mc) (hNc : KFlat X.O Nc)
    (γ : DerivedCategory.Q.obj (Mc ⊗ Nc) ≅ DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (Mod X.O) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (γ' : DerivedCategory.Q.obj (Nc ⊗ Mc) ≅ DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (Mod X.O) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    ∃ E : Complexes X.O, X.IsPerfectComplex E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj Mc) := by
  let := derivedMonoidal X.O
  exact isPerfect_of_isInvertibleObject_standard (DerivedCategory.Q.obj Mc)
    ⟨⟨DerivedCategory.Q.obj Nc,
      (symmetricMonoidalDerived X.O).comparison Mc Nc hMc hNc ≪≫ γ ≪≫
        (symmetricMonoidalDerived X.O).unitIso.symm,
      (symmetricMonoidalDerived X.O).comparison Nc Mc hNc hMc ≪≫ γ' ≪≫
        (symmetricMonoidalDerived X.O).unitIso.symm⟩⟩

end Standard

section AnyModel

variable [hd : HasDerivedCategory.{d} (Mod X.O)]

/-- **An invertible object of `D(O)` is perfect.** This is the step of the source's proof of
`(1) ⟹ (2)` of Stacks 0FPY which concludes, from Stacks 0FPV, that an object with an inverse is
perfect. It holds for any model of `D(O)`: see the implementation notes. -/
theorem isPerfect_of_isInvertibleObject (M : DerivedCategory (Mod X.O))
    (hM : IsInvertibleObject X M) :
    X.IsPerfect M := by
  let := derivedMonoidal X.O
  obtain ⟨H⟩ := hM
  obtain ⟨Mc, κ, hMc, hκ⟩ := exists_kFlat_resolution X.O (DerivedCategory.Q.objPreimage M)
  obtain ⟨Nc, κ', hNc, hκ'⟩ := exists_kFlat_resolution X.O (DerivedCategory.Q.objPreimage H.inv)
  have hMc' : KFlat X.O Mc := hMc
  have hNc' : KFlat X.O Nc := hNc
  let αM : DerivedCategory.Q.obj Mc ≅ M :=
    asIso (DerivedCategory.Q.map κ) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  let αN : DerivedCategory.Q.obj Nc ≅ H.inv :=
    asIso (DerivedCategory.Q.map κ') ≪≫ DerivedCategory.Q.objObjPreimageIso H.inv
  let γ := ((symmetricMonoidalDerived X.O).comparison Mc Nc hMc' hNc').symm ≪≫
    tensorIso αM αN ≪≫ H.isoLeft ≪≫ (symmetricMonoidalDerived X.O).unitIso
  let γ' := ((symmetricMonoidalDerived X.O).comparison Nc Mc hNc' hMc').symm ≪≫
    tensorIso αN αM ≪≫ H.isoRight ≪≫ (symmetricMonoidalDerived X.O).unitIso
  obtain ⟨E, hE, ⟨eE⟩⟩ := exists_isPerfectComplex_of_tensorIsoUnit_standard Mc Nc hMc' hNc'
    (qObjIsoOfModel hd (HasDerivedCategory.standard (Mod X.O)) γ)
    (qObjIsoOfModel hd (HasDerivedCategory.standard (Mod X.O)) γ')
  exact ⟨E, hE, ⟨qObjIsoOfModel (HasDerivedCategory.standard (Mod X.O)) hd eE ≪≫ αM⟩⟩

/-- **Stacks 0FPY.** Let `(C, O)` be a ringed site and let `M` be an object of `D(O)`. The
following are equivalent:

1. `M` is invertible in `D(O)` (`IsInvertibleObject`: Stacks 0FFN for the derived tensor product
   of Stacks 0FPT);
2. there is a locally finite direct product decomposition `O = ∏_{n ∈ ℤ} O_n` and for each `n` an
   invertible `O_n`-module `ℋ^n` (Stacks 0409) with `M = ⨁ ℋ^n[-n]` in `D(O)`
   (`HasInvertibleModuleDecomposition`).

If they hold, `M` is a perfect object of `D(O)` (`AlgebraicGeometry.RingedSite.IsPerfect`,
Stacks 08G5). If `(C, O)` is a locally ringed site (Stacks 04EU) they are also equivalent to

3. for every object `U` of `C` there are a covering `{U_i → U}` and integers `n_i` such that
   `M|_{U_i}` is isomorphic in `D(O_{U_i})` to an invertible `O_{U_i}`-module placed in degree
   `n_i` (`HasLocalInvertibleDegree`).

`D(O)` is any model of the derived category. The ringed site has its objects, its morphisms and
its rings of sections in one universe; see the note of the `stacks` attribute. -/
@[stacks 0FPY "All of the tag: (1) ⟺ (2) on every ringed site; (1) implies that M is perfect; \
and (1) ⟺ (2) ⟺ (3) on a locally ringed site. The ringed site is RingedSite.{u, u, u} -- \
objects, morphisms and sections of O in one universe u. This is the library's one-universe \
convention for D(O) as a symmetric monoidal category: the derived tensor product of Stacks 0FPT \
on a ringed site (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal) is built from the \
K-flat resolutions of Stacks 06YS, which the library constructs at that universe pattern only, \
so clause (1) has no meaning off it. The four HasSheafify / WEqualsLocallyBijective instance \
arguments are the library's standard ones, and Mathlib synthesizes all four for every \
RingedSite.{u, u, u}"]
theorem isInvertibleObject_tfae (M : DerivedCategory (Mod X.O)) :
    [IsInvertibleObject X M, HasInvertibleModuleDecomposition X M].TFAE ∧
      (IsInvertibleObject X M → X.IsPerfect M) ∧
      (IsLocallyRinged X →
        [IsInvertibleObject X M, HasInvertibleModuleDecomposition X M,
          HasLocalInvertibleDegree X M].TFAE) := by
  have h12 : IsInvertibleObject X M ↔ HasInvertibleModuleDecomposition X M := by
    refine ⟨fun hM => ?_, isInvertibleObject_of_hasInvertibleModuleDecomposition M⟩
    let := derivedMonoidal X.O
    obtain ⟨H⟩ := hM
    exact hasInvertibleModuleDecomposition_of_tensorIsoUnit M H.inv H.isoLeft
      (isPerfect_of_isInvertibleObject M ⟨H⟩)
      (isPerfect_of_isInvertibleObject H.inv ⟨⟨M, H.isoRight, H.isoLeft⟩⟩)
  refine ⟨?_, isPerfect_of_isInvertibleObject M, fun hloc => ?_⟩
  · tfae_have 1 ↔ 2 := h12
    tfae_finish
  · tfae_have 1 ↔ 2 := h12
    tfae_have 2 ↔ 3 := hasInvertibleModuleDecomposition_iff_hasLocalInvertibleDegree M hloc
    tfae_finish

end AnyModel

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
