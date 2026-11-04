module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueField
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistSections
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwists
public import StacksFrontier.AlgebraicGeometry.Surfaces.RestrictedNegativeTwistSections
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhoodSupplement
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueFieldSupplement

/-!
# The sections of the twist an exceptional curve cuts out are the sections of `𝒪(m)`

Let `E ⊆ X` be an exceptional curve of the first kind, cut out by an ideal sheaf `D` and
presented as the projective line by an isomorphism `e : 𝐏¹_k ≅ E`.
`StacksFrontier/AlgebraicGeometry/Surfaces/RestrictedNegativeTwistSections.lean` identifies the
kernel of the restriction `Γ(Eₘ₊₁, 𝒪) ⟶ Γ(Eₘ, 𝒪)` with the global sections of
`𝒪_X(-D ^ m)|_D`, the module `Stacks.Divisors.restrictedNegativeTwist (D ^ m) D`. This file
computes those sections: they are the global sections of `𝒪(m)` on `𝐏¹_k`, `k`-linearly, and so
form a `k`-vector space of dimension `m + 1`.

The transport is an assembly of three identifications. `𝒪_X(-D ^ m)|_D` is a direct image
along the inclusion `i : E ⟶ X`, so its sections over `X` *are* the sections over `E` of what is
pushed forward, `Stacks.Cohomology.AffineBase.pushforwardSectionsIso`, which is `Iso.refl`.
Along the isomorphism `e` the sections over `E` are the sections over `𝐏¹_k` of the pullback,
because the unit `N ⟶ e_*e^*N` of the pullback–pushforward adjunction is an isomorphism for an
isomorphism of schemes, `Stacks.ClosedImmersion.sectionsIsoPullbackOfIsIso`. And that pullback
is `𝒪(m)`, by `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf` — non-canonically, which is all a
dimension count needs.

## The scalars

The three steps are linear over three different rings: `Γ(X, 𝒪_X)`, `Γ(E, 𝒪_E)` and
`Γ(𝐏¹_k, 𝒪)`. The common scalars are `k`, which acts through
`AlgebraicGeometry.Scheme.IdealSheafData.sectionsSubschemeRingEquivOfIso`, the identification
`Γ(E, 𝒪_E) ≅ k` of `Γ(𝐏¹_k, 𝒪) = k`. The one thing to check is that the two routes from `k` to
`Γ(𝐏¹_k, 𝒪)` — through `Γ(E, 𝒪_E)` and along `e`, or directly as the coefficients of the graded
polynomial ring — agree; that is
`AlgebraicGeometry.Scheme.IdealSheafData.appTop_eq_coeffScalar_sectionsSubschemeRingEquivOfIso`,
and it holds because both are the same ring equivalence read in two directions.

## What this is for, and what it does not give

This is the `k`-side half of the identification of the graded piece `Iₘ / Iₘ₊₁` of the
projection-kernel filtration with the binary forms of degree `m` that the Stacks proof of
[Stacks, Tag 0C2K] uses. The other half is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.exists_addMonoidHom_smul_formalNeighborhoodProjection_graded`, which exhibits the graded piece
and these sections as the same additive group and records the compatibility of the scalars: the
additive map comes from the `𝒪_X`-linear short exact sequence of [Stacks, Tag 0C4T], while the
action of `k = Γ(E, 𝒪_E)` on the graded piece is multiplication inside `Γ(Eₘ₊₁, 𝒪)`, and since
`𝒪_X ⟶ i_*𝒪_E` is only locally surjective a scalar in `k` need not be the restriction of a
global function on `X`. The comparison is therefore made on an affine cover, in
`Stacks.Divisors.app_mul_of_smul_inclusion_appTop`.

What is **not** here is the multiplicativity of the identification *across* degrees: the twist
comparison used below is non-canonical, one degree at a time, so nothing here says that the
product of a degree-one and a degree-`m` symbol is the degree-`(m + 1)` symbol of the product.
That is what degree-one generation of the associated graded ring — the `hgen` input of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofDegreewiseSymbol` — needs, and
it is supplied in
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistMultiplicative.lean`, which does not
make this family compatible either: it assembles the comparison in the degree of a product out of
the two factors' choices instead.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.restrictedNegativeTwistSections` — the global
  sections of `𝒪_X(-D ^ m)|_D`, as a `k`-module through `Γ(E, 𝒪_E) ≅ k`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.sections_pushforward_top_eq` — the sections of a
  direct image over the whole target are the sections of the source.
* `AlgebraicGeometry.Scheme.IdealSheafData.sections_restrictedNegativeTwist_eq` — the sections
  of the sealed module `𝒪_X(-D ^ m)|_D` are the sections over `E` of the pullback of the ideal
  sheaf, so the `k`-module below is a `k`-module structure on them.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.restrictedNegativeTwistSectionsEquivTwist` — **`Γ(X, 𝒪_X(-D ^ m)|_D) ≅ H⁰(𝐏¹_k, 𝒪(m))`**,
  `k`-linearly.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.finrank_restrictedNegativeTwistSections` — **those sections have dimension `m + 1` over
  `k`.**

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Divisors Stacks.ProjectiveSpace.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The two crossings of a direct image -/

/-- **The sections of a direct image over the whole target are the sections of the source.**
This is `Stacks.Cohomology.AffineBase.pushforwardSectionsIso` read on underlying groups: the
sections of `f_*M` over `⊤` are by definition the sections of `M` over `f⁻¹⊤ = ⊤`. -/
public theorem sections_pushforward_top_eq {X Y : Scheme.{u}} (f : Y ⟶ X) (M : Y.Modules) :
    Γ((Scheme.Modules.pushforward f).obj M, (⊤ : X.Opens)) = Γ(M, (⊤ : Y.Opens)) :=
  rfl

variable {X : Scheme.{u}}

/-- **The sections of `𝒪_X(-D ^ m)|_D` are the sections over the subscheme of the pullback of
the ideal sheaf.** By `Stacks.Divisors.restrictedNegativeTwist_eq` the module is the direct
image along `D.subschemeι` of that pullback, and
`AlgebraicGeometry.Scheme.IdealSheafData.sections_pushforward_top_eq` identifies the sections of
a direct image. -/
public theorem sections_restrictedNegativeTwist_eq (D : X.IdealSheafData) (m : ℕ) :
    Γ(restrictedNegativeTwist (D ^ m) D, (⊤ : X.Opens)) =
      Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)),
        (⊤ : D.subscheme.Opens)) := by
  rw [restrictedNegativeTwist_eq]
  exact sections_pushforward_top_eq _ _

/-! ### The sections as a `k`-module -/

/-- **The global sections of `𝒪_X(-D ^ m)|_D`, as a `k`-module.** The module is a direct image
along the inclusion of the subscheme, so by
`AlgebraicGeometry.Scheme.IdealSheafData.sections_restrictedNegativeTwist_eq` its global
sections on `X` are the global sections on the subscheme of the pullback of the ideal sheaf,
and those are a module over `Γ(E, 𝒪_E)`, which is `k` by
`AlgebraicGeometry.Scheme.IdealSheafData.sectionsSubschemeRingEquivOfIso`. -/
public def restrictedNegativeTwistSections (D : X.IdealSheafData) (k : Type u) [Field k]
    (e : projectiveLineProj k ≅ D.subscheme) (m : ℕ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (sectionsSubschemeRingEquivOfIso D k e).symm.toRingHom).obj
    ((Stacks.Cohomology.sectionsFunctor D.subscheme ⊤).obj
      ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m))))

variable {D : X.IdealSheafData} {k : Type u} [Field k]
  {e : projectiveLineProj k ≅ D.subscheme}

/-- **The two routes from `k` to the global functions on `𝐏¹_k` agree.** Pulling a global
function on the subscheme back along `e` is reading it as a coefficient by
`AlgebraicGeometry.Scheme.IdealSheafData.sectionsSubschemeRingEquivOfIso` and then pushing that
coefficient forward by `Stacks.ProjectiveSpace.Cohomology.coeffScalar`: both are
`Stacks.ProjectiveSpace.Cohomology.coeffRingEquivGlobalSections` read in two directions. -/
public theorem appTop_eq_coeffScalar_sectionsSubschemeRingEquivOfIso (y : Γ(D.subscheme, ⊤)) :
    (e.hom.appTop).hom y = coeffScalar k 1 (sectionsSubschemeRingEquivOfIso D k e y) :=
  ((coeffRingEquivGlobalSections k 1).apply_symm_apply _).symm

/-- The scalar `c` of `k`, read as a global function on the subscheme and pulled back along `e`,
is `c` read as a coefficient on `𝐏¹_k`. -/
public theorem appTop_symm_sectionsSubschemeRingEquivOfIso (c : k) :
    (e.hom.appTop).hom ((sectionsSubschemeRingEquivOfIso D k e).symm c) = coeffScalar k 1 c := by
  rw [appTop_eq_coeffScalar_sectionsSubschemeRingEquivOfIso, RingEquiv.apply_symm_apply]

namespace IsExceptionalCurveOfFirstKind

/-! ### The transport -/

/-- **`Γ(X, 𝒪_X(-D ^ m)|_D) ≅ H⁰(𝐏¹_k, 𝒪(m))`, `k`-linearly.** For an exceptional curve of the
first kind the sections over `E` of the pullback of `𝒪_X(-mE)` are the sections over `𝐏¹_k` of
its further pullback along `e`, by
`Stacks.ClosedImmersion.sectionsIsoPullbackOfIsIso`, and that further pullback is the `m`-th
twist, by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf`. The composite is linear over
`Γ(E, 𝒪_E)`, and the two actions of `k` match by
`AlgebraicGeometry.Scheme.IdealSheafData.appTop_symm_sectionsSubschemeRingEquivOfIso`.

The twist comparison is non-canonical, so this equivalence is too; only the dimension it
computes is used. -/
public def restrictedNegativeTwistSectionsEquivTwist
    (hE : IsExceptionalCurveOfFirstKind D k e) (m : ℕ) :
    restrictedNegativeTwistSections D k e m ≃ₗ[k]
      (ModuleCat.restrictScalars.{u} (coeffScalar k 1)).obj
        ((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).obj
          (ProjectiveSpectrum.Proj.twistingSheaf
            (MvPolynomial.homogeneousSubmodule (Fin 2) k) (m : ℤ))) :=
  let g : (Stacks.Cohomology.sectionsFunctor D.subscheme ⊤).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m))) ≅
      (ModuleCat.restrictScalars (e.hom.appTop).hom).obj
        ((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).obj
          (ProjectiveSpectrum.Proj.twistingSheaf
            (MvPolynomial.homogeneousSubmodule (Fin 2) k) (m : ℤ))) :=
    Stacks.ClosedImmersion.sectionsIsoPullbackOfIsIso e.hom
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m))) ≪≫
      (ModuleCat.restrictScalars (e.hom.appTop).hom).mapIso
        ((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).mapIso
          (hE.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf m).some)
  AddEquiv.toLinearEquiv g.toLinearEquiv.toAddEquiv fun c x => by
    refine (g.toLinearEquiv.map_smul
      ((sectionsSubschemeRingEquivOfIso D k e).symm c) x).trans ?_
    exact congrArg (· • g.toLinearEquiv x) (appTop_symm_sectionsSubschemeRingEquivOfIso c)

/-- **The sections of `𝒪_X(-D ^ m)|_D` form a `k`-vector space of dimension `m + 1`.** They are
the global sections of `𝒪(m)` on the projective line, which are free of rank `m + 1` on the
degree-`m` monomials in the two coordinates by
`AlgebraicGeometry.projectiveLineProjTwistSectionsBasis`.

This is the dimension the Stacks proof of [Stacks, Tag 0C2K] asks of the graded piece
`Iₘ / Iₘ₊₁`; transporting it there needs the `k`-linearity discussed in the module docstring. -/
public theorem finrank_restrictedNegativeTwistSections
    (hE : IsExceptionalCurveOfFirstKind D k e) (m : ℕ) :
    Module.finrank k (restrictedNegativeTwistSections D k e m) = m + 1 := by
  rw [(hE.restrictedNegativeTwistSectionsEquivTwist m).finrank_eq,
    Module.finrank_eq_card_basis
      (projectiveLineProjTwistSectionsBasis k (m : ℤ) (Int.natCast_nonneg m))]
  simp

end IsExceptionalCurveOfFirstKind

end AlgebraicGeometry.Scheme.IdealSheafData

end
