module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedCurryRestriction

/-!
# A roof with a tensor factor, from a system inverted on an open

Let `(C, O)` be a ringed site and `U` a subterminal object of `C` — for a topological space, an
open. Let `aᵢ : Iᵢ ⟶ O'` be a family of morphisms of `D(O)` to a fixed object `O'`, each becoming
invertible after restriction to `C/U`, and suppose every morphism `O'|_U ⟶ R𝓗om(E, E')|_U` is the
restriction of a morphism `Iᵢ ⟶ R𝓗om(E, E')` precomposed with `aᵢ|_U`, for some `i`. Suppose
finally that `O'` is a unit for the derived tensor product against `E`, in the sense that some
`v : O' ⟶ R𝓗om(E, E)` has invertible transpose `O' ⊗^𝐋_O E ⟶ E`.

Then for every `E'` and every `α : E|_U ⟶ E'|_U` there are an index `i` and a roof

`E ←β— Iᵢ ⊗^𝐋_O E —γ→ E'`

with `β|_U` invertible and `γ|_U = β|_U ≫ α`, that is, `α = γ|_U ∘ (β|_U)⁻¹`.

This is [Stacks, Tag 08EH] with its two geometric inputs — invertibility of the system on the open
and surjectivity of the comparison of [Stacks, Tag 08DC] — taken as hypotheses, so that the
argument runs with no concrete site in the terms. On `X = Spec A` the hypotheses are the Koszul
system on the powers of `f₁, …, f_r`, the structure sheaf in degree zero, and [Stacks, Tag 08DD].

## Main results

* `Stacks.Cohomology.SliceDerivedSheafHom.derivedCurryHomEquiv_comp_mate_of_map_eq`: the
  naturality step. If `w = a|_U ≫ ψ`, the transpose over `C/U` of `w` is `a|_U ⊗ 1_{E|_U}`
  followed by the transpose of `ψ`.
* `Stacks.Cohomology.SliceDerivedSheafHom.map_derivedCurryHomEquiv_of_map_eq`: the computation
  both legs of the roof run on. For `ζ : K ⟶ R𝓗om(E, Z)` whose restriction composed with the mate
  is `a|_U ≫ ψ`, the restriction of the transpose of `ζ` is the slice tensor comparison, followed
  by `a|_U ⊗ 1_{E|_U}`, followed by the transpose over `C/U` of `ψ`. Only the last factor depends
  on `ζ`, which is what makes the two legs comparable.
* `Stacks.Cohomology.SliceDerivedSheafHom.isIso_derivedCurryHomEquiv_restrict_of_isIso`:
  invertibility of the transpose of `v` passes to the transpose over `C/U` of `v|_U` followed by
  the mate. This is what makes the left leg invertible on `C/U`.
* `Stacks.Cohomology.SliceDerivedSheafHom.exists_comp_derivedSheafHomRestrictionTranspose_eq` and
  `Stacks.Cohomology.SliceDerivedSheafHom.exists_derivedCurryHomEquiv_comp_mate_eq`: the mate is
  invertible and the bijection of [Stacks, Tag 08J8] is a bijection, so every morphism
  `O'|_U ⊗^𝐋 E|_U ⟶ E'|_U` is the transpose over `C/U` of some `ψ : O'|_U ⟶ R𝓗om_O(E, E')|_U`
  followed by the mate. This is what feeds such a morphism to a factorisation hypothesis phrased,
  as [Stacks, Tag 08DC] phrases it, on `R𝓗om_O(E, E')|_U`.
* `Stacks.Cohomology.SliceDerivedSheafHom.exists_roof_of_exists_factorisation`: the roof.

## Why the mate rather than [Stacks, Tag 08DL]

The comparison `R𝓗om_O(E, E')|_U ⟶ R𝓗om_{O|_U}(E|_U, E'|_U)` used here is the canonical transpose
of [Stacks, Tag 08I3],
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose`, invertible by
`Stacks.Cohomology.SliceDerivedSheafHom.isIso_derivedSheafHomRestrictionTranspose` — not the
comparison of [Stacks, Tag 08DL]. That the two agree is the *mate statement*, which is unproved in
this development, and nothing below needs it: what is used is that the transpose is invertible and
that the bijection of [Stacks, Tag 08J8] commutes with restriction through it, which is
`Stacks.Cohomology.SliceDerivedSheafHom.map_derivedCurryHomEquiv`.

## Implementation notes

**What makes the argument expensive, and how it is kept in budget.** No elaborator option is
raised anywhere in this file. What costs the elaborator is not the mathematics but the
tensor–internal-hom bijection of [Stacks, Tag 08J8] *at the slice site* `C/U`: each mention of
`AlgebraicGeometry.(@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) …` synthesizes the eight instance
arguments of that bijection at `X.over U` — the spellings `(X.over U).O` and `X.O.over U` do not
agree at the transparency instance search uses, so the variables of this file are not found and
the arguments are rebuilt — and the terms so built are deep enough that comparing two of them is
within a small factor of the default recursion limit. Abstracting the ambient ringed site — which
is why this file is stated for a variable `X` rather than for `Spec A` — removes the concrete site
from the terms but not that bijection.

Three things keep the argument inside the default budgets, and all three are about *how often that
bijection is written down and what is then done with it*:

* the morphism fed to the factorisation hypothesis is obtained opaquely, as the witness of
  `Stacks.Cohomology.SliceDerivedSheafHom.exists_derivedCurryHomEquiv_comp_mate_eq`, instead of
  being written as an inverse image under the bijection composed with the inverse of the mate.
  That composite occurred three times in the roof and each occurrence was re-elaborated;
* the invertibility of the mate is used in
  `Stacks.Cohomology.SliceDerivedSheafHom.exists_comp_derivedSheafHomRestrictionTranspose_eq`,
  whose statement does not mention the bijection at all, so the cancellation
  `(ψ ≫ t⁻¹) ≫ t = ψ` is rewritten in a goal whose only large subterms are the ambient objects;
* the two legs are compared with `reassoc_of%` rather than by rewriting with `Category.assoc`.
  Searching for `(f ≫ g) ≫ h` in a goal of this size costs more than the rest of the proof,
  whereas `reassoc_of% hβ` reassociates an equation already in hand.

Correspondingly, an equation between two independently elaborated mentions of the bijection should
be consumed by `rw`, which matches subterm against subterm, and not by `exact` against the
hypothesis of another declaration, which compares the two whole propositions and exceeds the
default recursion limit.

## References

* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08DC](https://stacks.math.columbia.edu/tag/08DC)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction)

universe u

namespace Stacks.Cohomology.SliceDerivedSheafHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]

/-! ### Why every slice functor below is written with its instances pinned

`AlgebraicGeometry.RingedSite.over` is `@[implicit_reducible]`, so `(X.over U).J` and `X.J.over U`
are the same topology by `rfl`, and `(X.over U).O` and `X.O.over U` the same structure sheaf — but
not at the transparency instance search uses, so a slice functor written plainly as `… (X.over U)`
does not find this file's hypotheses and builds a second witness. The imported slice declarations
disagree on which spelling they carry, which is issue #1226 of the ring-sheaf canonicalisation;
`SliceDerivedCurryRestriction.lean` records the diagnosis.

Every slice functor below is therefore applied with `@` and its instance arguments given as
`inferInstance` at `X.J.over U` / `X.O.over U`, the spelling
`SliceDerivedSheafHomTranspose.lean` pins at, so that this file and everything it composes with
agree on the nose. Do not replace such an application by the plain `… (X.over U)` form — the file
does not then elaborate inside the default budgets. -/

omit [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- **The transpose over `C/U` of a morphism that factors through `a|_U`.** For `a : K ⟶ O'`,
`w : K|_U ⟶ R𝓗om_{O|_U}(E|_U, Z|_U)` and `ψ : O'|_U ⟶ R𝓗om_{O|_U}(E|_U, Z|_U)` with
`w = a|_U ≫ ψ`, the transpose over `C/U` of `w` is `a|_U ⊗ 1_{E|_U}` followed by the transpose of
`ψ`. This is the naturality of the bijection of [Stacks, Tag 08J8] in its source. -/
theorem derivedCurryHomEquiv_comp_mate_of_map_eq
    (K O' E Z : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : K ⟶ O')
    (w : (restrictD X U).obj K ⟶
      ((@AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor (X.over U)
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).obj
        (op ((restrictD X U).obj E))).obj ((restrictD X U).obj Z))
    (ψ : (restrictD X U).obj O' ⟶
      ((@AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor (X.over U)
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).obj
        (op ((restrictD X U).obj E))).obj ((restrictD X U).obj Z))
    (hw : w = (restrictD X U).map a ≫ ψ) :
    (@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj K)
        ((restrictD X U).obj E) ((restrictD X U).obj Z) w =
      ((@Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).map
          ((restrictD X U).map a)).app ((restrictD X U).obj E) ≫
        (@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj O')
          ((restrictD X U).obj E) ((restrictD X U).obj Z) ψ := by
  rw [hw, (@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source' (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ)))
    ((restrictD X U).obj O') ((restrictD X U).obj K) ((restrictD X U).obj E)
    ((restrictD X U).obj Z) ((restrictD X U).map a) ψ]

/-- **The restriction to `C/U` of the transpose of a map whose restriction factors through `a`.**
It is the slice tensor comparison, followed by `a|_U ⊗ 1_{E|_U}`, followed by the transpose over
`C/U` of `ψ`.

Only the last factor depends on `ζ`, which is what makes two legs of a roof built this way
comparable. -/
theorem map_derivedCurryHomEquiv_of_map_eq
    (K O' E Z : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : K ⟶ O')
    (ζ : K ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op E)).obj Z)
    (ψ : (restrictD X U).obj O' ⟶
      ((@AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor (X.over U)
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).obj
        (op ((restrictD X U).obj E))).obj ((restrictD X U).obj Z))
    (hζ : (restrictD X U).map ζ ≫ derivedSheafHomRestrictionTranspose X U E Z =
      (restrictD X U).map a ≫ ψ) :
    (restrictD X U).map (RingedSite.derivedCurryHomEquiv X K E Z ζ) =
      (sliceTensorRestrictionObjIso X U K E).hom ≫
        ((@Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).map
            ((restrictD X U).map a)).app ((restrictD X U).obj E) ≫
          (@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj O')
            ((restrictD X U).obj E) ((restrictD X U).obj Z) ψ := by
  rw [map_derivedCurryHomEquiv X U K E Z ζ,
    derivedCurryHomEquiv_comp_mate_of_map_eq X U K O' E Z a
      ((restrictD X U).map ζ ≫ derivedSheafHomRestrictionTranspose X U E Z) ψ hζ]

variable [HasBinaryProducts X.C] [IsIso (Over.forgetAdjStar U).unit]

omit [HasBinaryProducts X.C] [IsIso (Over.forgetAdjStar U).unit] in
/-- **Invertibility of the transpose passes to the slice site.** If the transpose
`O' ⊗^𝐋_O E ⟶ E` of `v : O' ⟶ R𝓗om_O(E, E)` is invertible, then so is the transpose over `C/U` of
`v|_U` followed by the mate: the two differ by the slice tensor comparison, by
`Stacks.Cohomology.SliceDerivedSheafHom.map_derivedCurryHomEquiv`. -/
theorem isIso_derivedCurryHomEquiv_restrict_of_isIso
    (O' E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (v : O' ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op E)).obj E)
    (hv : IsIso (RingedSite.derivedCurryHomEquiv X O' E E v)) :
    IsIso ((@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj O')
      ((restrictD X U).obj E) ((restrictD X U).obj E)
      ((restrictD X U).map v ≫ derivedSheafHomRestrictionTranspose X U E E)) := by
  have := hv
  have : IsIso ((sliceTensorRestrictionObjIso X U O' E).hom ≫
      (@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj O')
        ((restrictD X U).obj E) ((restrictD X U).obj E)
        ((restrictD X U).map v ≫ derivedSheafHomRestrictionTranspose X U E E)) := by
    rw [← map_derivedCurryHomEquiv X U O' E E v]
    exact Functor.map_isIso _ _
  exact IsIso.of_isIso_comp_left (sliceTensorRestrictionObjIso X U O' E).hom _

/-- **Every morphism into `R𝓗om_{O|_U}(E|_U, E'|_U)` comes from one into
`R𝓗om_O(E, E')|_U` through the mate.** The mate is invertible, by
`Stacks.Cohomology.SliceDerivedSheafHom.isIso_derivedSheafHomRestrictionTranspose`, so
precomposition with it is surjective. -/
theorem exists_comp_derivedSheafHomRestrictionTranspose_eq
    (O' E E' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ψ' : (restrictD X U).obj O' ⟶
      ((@AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor (X.over U)
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).obj
        (op ((restrictD X U).obj E))).obj ((restrictD X U).obj E')) :
    ∃ ψ : (restrictD X U).obj O' ⟶
        (restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op E)).obj E'),
      ψ ≫ derivedSheafHomRestrictionTranspose X U E E' = ψ' := by
  have := @Stacks.Cohomology.SliceDerivedSheafHom.isIso_derivedSheafHomRestrictionTranspose X U
    (inferInstance : HasSheafify X.J AddCommGrpCat.{u})
    (inferInstance : X.J.WEqualsLocallyBijective AddCommGrpCat.{u})
    (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
    (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
    (inferInstance : (sheafTensor.{u, u, u, u, u} X.O).Additive)
    (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive)
    (inferInstance : ∀ K L : CochainComplex (Modules X.O) ℤ,
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O)
        (ComplexShape.up ℤ))
    (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
    (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
    (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
        (ComplexShape.up ℤ))
    (inferInstance : HasBinaryProducts X.C)
    (inferInstance : IsIso (Over.forgetAdjStar U).unit) E E'
  refine ⟨ψ' ≫ inv (derivedSheafHomRestrictionTranspose X U E E'), ?_⟩
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **Every morphism out of `O'|_U ⊗^𝐋 E|_U` is the transpose of a morphism through the mate.**
For `g : O'|_U ⊗^𝐋_{O|_U} E|_U ⟶ E'|_U` there is a `ψ : O'|_U ⟶ R𝓗om_O(E, E')|_U` whose
composite with the mate has transpose `g` over `C/U`: the mate is invertible, by
`Stacks.Cohomology.SliceDerivedSheafHom.isIso_derivedSheafHomRestrictionTranspose`, and the
bijection of [Stacks, Tag 08J8] is a bijection.

This is what lets the compatibility clause of [Stacks, Tag 08EH] be fed to a factorisation
hypothesis stated, as [Stacks, Tag 08DC] states it, for morphisms into the *restriction* of the
internal hom rather than into the internal hom of the restrictions. -/
theorem exists_derivedCurryHomEquiv_comp_mate_eq
    (O' E E' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (g : ((@Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).obj
        ((restrictD X U).obj O')).obj ((restrictD X U).obj E) ⟶ (restrictD X U).obj E') :
    ∃ ψ : (restrictD X U).obj O' ⟶
        (restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op E)).obj E'),
      (@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj O')
          ((restrictD X U).obj E) ((restrictD X U).obj E')
          (ψ ≫ derivedSheafHomRestrictionTranspose X U E E') = g := by
  obtain ⟨ψ, hψ⟩ := exists_comp_derivedSheafHomRestrictionTranspose_eq X U O' E E'
    (((@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj O')
      ((restrictD X U).obj E) ((restrictD X U).obj E')).symm g)
  exact ⟨ψ, by rw [hψ, AddEquiv.apply_symm_apply]⟩

/-- **The roof of [Stacks, Tag 08EH], with its geometric inputs as hypotheses.** Let
`aᵢ : Iᵢ ⟶ O'` be morphisms of `D(O)` becoming invertible on `C/U`, let `v : O' ⟶ R𝓗om(E, E)`
have invertible transpose `O' ⊗^𝐋_O E ⟶ E`, and suppose every
`φ : O'|_U ⟶ R𝓗om(E, E')|_U` is `aᵢ|_U` followed by the restriction of some
`ξ : Iᵢ ⟶ R𝓗om(E, E')`. Then every `α : E|_U ⟶ E'|_U` fits into a roof
`E ←β— Iᵢ ⊗^𝐋_O E —γ→ E'` with `β|_U` invertible and `γ|_U = β|_U ≫ α`.

`β` is the transpose of `aᵢ ≫ v` and `γ` that of `ξ`, so both restrictions are computed by
`Stacks.Cohomology.SliceDerivedSheafHom.map_derivedCurryHomEquiv_of_map_eq` and share the factor
through which `aᵢ` enters; the compatibility is then the defining property of the `φ` chosen for
`α`, and that factor cancels. -/
theorem exists_roof_of_exists_factorisation {ι : Type*}
    (I : ι → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (O' E E' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : ∀ i, I i ⟶ O') (ha : ∀ i, IsIso ((restrictD X U).map (a i)))
    (v : O' ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op E)).obj E)
    (hv : IsIso (RingedSite.derivedCurryHomEquiv X O' E E v))
    (hfac : ∀ φ : (restrictD X U).obj O' ⟶
        (restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op E)).obj E'),
      ∃ (i : ι) (ξ : I i ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op E)).obj E'),
        (restrictD X U).map ξ = (restrictD X U).map (a i) ≫ φ)
    (α : (restrictD X U).obj E ⟶ (restrictD X U).obj E') :
    ∃ (i : ι)
      (β : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj (I i)).obj E ⟶ E)
      (γ : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj (I i)).obj E ⟶ E'),
      IsIso ((restrictD X U).map β) ∧
        (restrictD X U).map γ = (restrictD X U).map β ≫ α := by
  obtain ⟨ψ, hψ⟩ := exists_derivedCurryHomEquiv_comp_mate_eq X U O' E E'
    ((@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj O')
        ((restrictD X U).obj E) ((restrictD X U).obj E)
        ((restrictD X U).map v ≫ derivedSheafHomRestrictionTranspose X U E E) ≫ α)
  obtain ⟨i, ξ, hξ⟩ := hfac ψ
  have := ha i
  have := isIso_derivedCurryHomEquiv_restrict_of_isIso X U O' E v hv
  have : IsIso (((@Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).map
      ((restrictD X U).map (a i))).app ((restrictD X U).obj E)) := by
    have : IsIso ((@Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).map
        ((restrictD X U).map (a i))) := Functor.map_isIso _ _
    exact inferInstance
  have hβ := map_derivedCurryHomEquiv_of_map_eq X U (I i) O' E E (a i) (a i ≫ v)
    ((restrictD X U).map v ≫ derivedSheafHomRestrictionTranspose X U E E)
    (by rw [(restrictD X U).map_comp, Category.assoc])
  have hγ := map_derivedCurryHomEquiv_of_map_eq X U (I i) O' E E' (a i) ξ
    (ψ ≫ derivedSheafHomRestrictionTranspose X U E E') (by rw [hξ, Category.assoc])
  refine ⟨i, RingedSite.derivedCurryHomEquiv X (I i) E E (a i ≫ v),
    RingedSite.derivedCurryHomEquiv X (I i) E E' ξ, ?_, ?_⟩
  · rw [hβ]
    infer_instance
  · rw [hγ, hψ, (reassoc_of% hβ) α]

end Stacks.Cohomology.SliceDerivedSheafHom

end
