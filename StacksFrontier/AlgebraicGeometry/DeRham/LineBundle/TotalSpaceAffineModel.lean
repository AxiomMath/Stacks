module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceFiniteType
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TrivializingAffineCover

/-!
# The affine local model of the total space of a line bundle

Let `L` be an invertible module on a scheme `X` and let `π : 𝕃 ⟶ X` be the total space of `L`,
the relative spectrum of `Sym(L)`. Over an affine open `U` of `X` the inverse image `π^{-1}U` is
again affine, and this file identifies its ring of functions: it is the symmetric algebra
`Sym_{Γ(X, U)}(Γ(L, U))`, and if `L` is trivialized over `U` — so that `Γ(L, U)` is free of rank
one over `Γ(X, U)` — it is the polynomial ring `Γ(X, U)[T]` in the fibre coordinate.

This is the local model the affine computations of Section 50.10 of the source are carried out
in: adjoining one variable is the trivialization of a line bundle, so the affine Poincaré lemma
`PolynomialDeRham.quasiIso_incl` is the computation of [Stacks, Tag 0FUI] over a trivializing
affine open precisely because of the identification proved here.

## Main definitions

* `Stacks.LineBundle.Situation.chartIso`: **the affine local model of the total space** — over an
  affine open `U` of `X` the inverse image of `U` in `𝕃` is the spectrum of the ring
  `Γ(U, Sym(L))` of sections of the algebra sheaf. This is the chart of the relative spectrum of
  [Stacks, Tag 01LP].
* `Stacks.LineBundle.Situation.topIso` and `Stacks.LineBundle.Situation.sectionsIso`: the
  resulting identification of `Γ(U, Sym(L))` with the functions `Γ(𝕃, π^{-1}U)` on the inverse
  image.
* `Stacks.LineBundle.Situation.polynomialAlgEquiv`: for a basis of `Γ(L, U)` indexed by `PUnit`,
  the identification `Sym_{Γ(X, U)}(Γ(L, U)) ≅ Γ(X, U)[T]`.

## Main results

* `Stacks.LineBundle.Situation.symSectionsRingEquiv`: **the functions on the inverse image of an
  affine open `U` of `X` in the total space are `Sym_{Γ(X, U)}(Γ(L, U))`.**
* `Stacks.LineBundle.Situation.polynomialSectionsRingEquiv`: **over an affine open on which the
  line bundle is trivialized, the functions on the inverse image in the total space are the
  polynomial ring `Γ(X, U)[T]`** — the affine local model `π^{-1}U = Spec Γ(X, U)[T]`.
* `Stacks.LineBundle.Situation.polynomialSectionsRingEquiv_C`: **the affine local model carries
  the constants of `Γ(X, U)[T]` to the pullback along `π`**, so the fibre coordinate is a
  coordinate over the base: the identification is one of `Γ(X, U)`-algebras for the algebra
  structure that `π` itself puts on `Γ(𝕃, π^{-1}U)`. Its two halves are
  `Stacks.LineBundle.Situation.symSectionsRingEquiv_algebraMap`, the same statement before the
  fibre coordinate is chosen, and
  `Stacks.LineBundle.Situation.totalSpaceToBase_app_affine`, which reads `π^♯` over an affine
  open as the structure map of the algebra sheaf followed by
  `Stacks.LineBundle.Situation.sectionsIso`.

## What this is for, and what it is not

Nothing here carries a `@[stacks]` attribute. [Stacks, Tag 0FUI] asserts that
`Ω^•_{X/S} ⟶ π_*Ω^•_{𝕃/S}` is a quasi-isomorphism when `ℚ` acts on the base, and that
`H^*_{dR}(X/S) = H^*_{dR}(𝕃/S)`; neither is proved here, and neither follows from this file
alone. What this file supplies is the first of the inputs that the reduction of Tag 0FUI to its
affine case needs — the identification of the local model — and it is recorded separately because
the reduction has further inputs, whose state is as follows:

* the comparison of the *restriction* of `Ω^•_{X/S}` to an affine open `U ⊆ X` lying over an
  affine open `V ⊆ S` with the algebraic de Rham complex `Ω^•_{Γ(X,U)/Γ(S,V)}`, as a complex.
  This is now available, in abelian groups, as
  `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamSectionsAbComplexIso`; the globally affine
  statement it generalizes is
  `Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamSectionsComplexIso`, whose ring
  arguments are given objects of `CommRingCat` and whose sections are taken at the top open;
* the identification of the restriction of
  `Stacks.LineBundle.Situation.deRhamPushforward` to such an open with the ring-level inclusion
  `PolynomialDeRham.incl`, which is what would let `PolynomialDeRham.quasiIso_incl` be
  transported. Its *ring-level* half is `Stacks.LineBundle.Situation.polynomialSectionsRingEquiv_C`
  above: the two comparisons are read over one and the same ring map `Γ(X, U) → Γ(X, U)[T]`,
  namely `Polynomial.C`, rather than over unrelated ones. Its *sheaf-level* half is the
  naturality of `Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso` in the square of
  `π`, and that is available on the wedges `d a₁ ∧ ⋯ ∧ d a_p` of universal differentials, as
  `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardHom_formsSectionsIso_inv`.
  That computation is now also available as an equality of *maps*, in the abelian reading the tag
  consumes. Functoriality of
  `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamSectionsAbComplex` in the square — recorded
  here and in the module docstring of
  `StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquare` as not existing — is
  `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamSectionsAbSquareMap` of
  `StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquareComplex`. Its input is the
  canonical map of abelian sheaves
  `AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap` of
  `StacksFrontier.AlgebraicGeometry.DeRham.Functoriality`, which already existed, together with two
  identifications that hold by `rfl`: the complex of sections is the sections functor applied to
  the complex of abelian sheaves, and sections over `U` of a direct image along `f` are sections
  over `f^{-1}U`. Conjugated by the affine-open comparison at both ends it is
  `Stacks.AlgebraicGeometry.AffineOpenDeRham.ringDeRhamAbSquareMap`, pinned on the generators by
  `ringDeRhamAbSquareMap_f_ιMulti_d` and `ringDeRhamAbSquareMap_f_smul_ιMulti_d`; the spanning
  step is `ringDeRhamAb_hom_ext` there, so the `Module ℤ` instance failure recorded in that other
  docstring is no longer in the way. Which ring-level map it is needs nothing new either —
  `Stacks.KaehlerDifferentialSquare.map` carried to exterior powers by
  `ExteriorAlgebra.powMapₛₗ`, over the ring square
  `Stacks.AlgebraicGeometry.AffineOpenDeRham.appLE_square` — and the semilinearity of the
  conjugated map is
  `Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_pushforwardSections_smul`. What
  is still owed on this input is only that that ring-level composite be *named*, so that the
  identification can be stated against it rather than against whatever candidate a consumer has
  in hand;
* for the de Rham cohomology half, invertibility of
  `AlgebraicGeometry.Scheme.Hom.deRhamPushforwardToDerived`, i.e. the acyclicity of the direct
  image along `π` for the *abelian* pushforward rather than for the pushforward of
  `𝒪`-modules. The `𝒪`-module statement is
  `Stacks.LineBundle.Situation.rightAcyclic_pushforward_totalSpaceForms`; the transfer pattern is
  `Stacks.DeRhamDirectImage.relativePushforwardHigherIso`.

The gluing step itself is available: quasi-isomorphy of a complex of sheaves of modules is local
on the site, by `Stacks.SheafOfModules.quasiIso_of_coversTop`, and the cover to apply it to is
`Stacks.LineBundle.Situation.exists_affine_trivializing_cover_over_affine`. The mismatch
recorded here — `Stacks.LineBundle.Situation.deRhamPushforward` is a morphism of complexes of
**abelian** sheaves, because
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap` is, whereas the locality lemma is
stated for complexes of sheaves of modules over a fixed sheaf of rings — is no longer a reason
the two readings cannot be exchanged: `Stacks.SheafOfModules.quasiIso_toSheaf_map_iff` says that
a morphism of complexes of sheaves of modules is a quasi-isomorphism exactly when its image
under the forgetful functor to abelian sheaves is, and
`Stacks.SheafOfModules.quasiIso_toSheaf_map_of_coversTop` is the locality lemma with its
conclusion transported across that. Both are conditions on a morphism of complexes of *modules*,
so using them still asks that the comparison be exhibited as the image of one;
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap` is built degreewise as
`SheafOfModules.toSheaf.map` of
`AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom`, with the commutation
`AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom_comm_d`, but it is not stated as the
image of a morphism of complexes of modules.

What the gluing step wants and the development does not have is a bridge from a statement about
*sections over an affine open* to one about the *sheaf complex on that affine open*:
`Stacks.SheafOfModules.quasiIso_of_coversTop` asks for quasi-isomorphy of the degreewise
restriction to the slice over each member of the cover, which is a statement about sheaves, while
the affine-open comparison above is taken on sections over `U`.

**So the two genuine gaps for Tag 0FUI are these**, and no map is among them: (i) that bridge
from sections over an affine open to the sheaf complex on it, which
`Stacks.SheafOfModules.quasiIso_of_coversTop` demands; and (ii) acyclicity of the direct image
along `π` for the **abelian** pushforward, where only the `𝒪`-module statement
`Stacks.LineBundle.Situation.rightAcyclic_pushforward_totalSpaceForms` exists. The canonical map
itself, its chart-wise reading and the spanning step that pins it are all present; nothing below
should be read as saying otherwise.

## Implementation notes

The chart is the generic one of a relative spectrum,
`Stacks.RelativeSpec.GluedSpectrum.chartIsoPreimage`, instantiated at
`Stacks.LineBundle.Situation.relativeSpecSituation`; the three definitions below mirror
`Stacks.LineBundle.Situation.laurentChartIso`, `laurentTopIso` and `laurentSectionsIso` of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.GradedForms`, which are the same construction
for the complement of the zero section.

The trivialization enters as a `Module.Basis PUnit Γ(X, U) Γ(L, U)`, which is what a
trivialization of `L` over `U` gives on sections. It is taken as an argument rather than
extracted from `Stacks.LineBundle.Situation.exists_trivializing_affineOpen`, whose conclusion is
an isomorphism `L.over U ≅ unit` of sheaves of modules on the slice site over `U`: passing from
that to a basis of the sections needs the evaluation of a slice-level isomorphism at the terminal
object of the slice, which the development does not have in a reusable form.

`PUnit` is the index type because `SymmetricAlgebra.equivMvPolynomial` produces
`MvPolynomial κ R` for the index type `κ` of the basis, and `MvPolynomial.pUnitAlgEquiv` is
Mathlib's identification of the one-variable case with `Polynomial`.

## References

* [Stacks Project, Tag 0FUI](https://stacks.math.columbia.edu/tag/0FUI)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 062M](https://stacks.math.columbia.edu/tag/062M)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### The affine local model of the total space -/

/-- **The affine local model of the total space of a line bundle**: over an affine open `U` of
`X` the inverse image of `U` in the total space is the spectrum of the ring `Γ(U, Sym(L))` of
sections of the algebra sheaf. This is the chart of the relative spectrum of
[Stacks, Tag 01LP]. -/
def Situation.chartIso (U : D.X.affineOpens) :
    Spec (Stacks.RelativeSpec.AlgebraSheaf.sections D.algebraSheaf U.1) ≅
      (D.totalSpaceToBase ⁻¹ᵁ U.1).toScheme :=
  (Stacks.RelativeSpec.gluedSpectrum D.relativeSpecSituation).chartIsoPreimage U

/-- The global sections of the two sides of the affine local model of the total space. -/
def Situation.topIso (U : D.X.affineOpens) :
    Γ(Spec (Stacks.RelativeSpec.AlgebraSheaf.sections D.algebraSheaf U.1), ⊤) ≅
      Γ((D.totalSpaceToBase ⁻¹ᵁ U.1).toScheme, ⊤) where
  hom := (D.chartIso U).inv.appTop
  inv := (D.chartIso U).hom.appTop
  hom_inv_id := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  inv_hom_id := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]

/-- **The functions on the inverse image of an affine open `U` of `X` in the total space are
`Γ(U, Sym(L))`.** This is the local computation identifying `π_*𝒪_𝕃` with the symmetric algebra
of the line bundle, read on sections over an affine open. -/
def Situation.sectionsIso (U : D.X.affineOpens) :
    Stacks.RelativeSpec.AlgebraSheaf.sections D.algebraSheaf U.1 ≅
      Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U.1) :=
  (Scheme.ΓSpecIso _).symm ≪≫ D.topIso U ≪≫ (D.totalSpaceToBase ⁻¹ᵁ U.1).topIso

/-! ### The symmetric algebra and the polynomial ring -/

/-- **The functions on the inverse image of an affine open `U` of `X` in the total space are the
symmetric algebra `Sym_{Γ(X, U)}(Γ(L, U))` of the sections of the line bundle.** -/
def Situation.symSectionsRingEquiv (U : D.X.affineOpens) :
    SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1) ≃+*
      Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U.1) :=
  (Stacks.SymAlgSections.ungradedSymSectionsRingEquiv D.L U.2).trans
    (D.sectionsIso U).commRingCatIsoToRingEquiv

/-- **The symmetric algebra of a module free of rank one is the polynomial ring in one
variable.** For the sections of a line bundle over a trivializing open this is the passage from
the intrinsic description of the total space to the fibre coordinate. -/
def Situation.polynomialAlgEquiv (U : D.X.affineOpens)
    (b : Module.Basis PUnit Γ(D.X, U.1) Γ(D.L, U.1)) :
    SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1) ≃ₐ[Γ(D.X, U.1)]
      Polynomial Γ(D.X, U.1) :=
  (SymmetricAlgebra.equivMvPolynomial b).trans (MvPolynomial.pUnitAlgEquiv _)

/-- **The affine local model `π^{-1}U = Spec Γ(X, U)[T]` of the total space over a trivializing
affine open**: if the sections of the line bundle over an affine open `U` of `X` are free of rank
one — which is what a trivialization of `L` over `U` gives — then the functions on the inverse
image of `U` in the total space are the polynomial ring `Γ(X, U)[T]` in one variable over the
functions on `U`.

This is the identification under which adjoining one variable, the subject of the affine
Poincaré lemma `PolynomialDeRham.quasiIso_incl`, is the local form of passing from `X` to the
total space of a line bundle on it. -/
def Situation.polynomialSectionsRingEquiv (U : D.X.affineOpens)
    (b : Module.Basis PUnit Γ(D.X, U.1) Γ(D.L, U.1)) :
    Polynomial Γ(D.X, U.1) ≃+* Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U.1) :=
  ((D.polynomialAlgEquiv U b).symm.toRingEquiv).trans (D.symSectionsRingEquiv U)

/-! ### The fibre coordinate and the structure morphism -/

/-- **Over an affine open `U` of `X` the universal map of [Stacks, Tag 01LX(3)] is the
comparison of the affine local model.** Both sides are
`(Scheme.ΓSpecIso _).inv ≫ (chartIsoPreimage U).inv.appTop ≫ (π^{-1}U).topIso.hom`: the left
is the map `Sym(L) ⟶ π_*𝒪_𝕃` of the relative spectrum, defined over every open, the right the
isomorphism `Situation.sectionsIso` of the affine local model. -/
theorem Situation.universalAlgebraMap_app_eq_sectionsIso (U : D.X.affineOpens) :
    (Stacks.RelativeSpec.universalAlgebraMap D.relativeSpecSituation).right.app (op U.1) =
      (D.sectionsIso U).hom :=
  Stacks.RelativeSpec.universalAlgebraMap_app D.relativeSpecSituation U

/-- **The structure morphism `π` of the total space, on sections over an affine open `U` of `X`,
is the structure map of the algebra sheaf followed by the comparison of the affine local
model.** This is `Stacks.RelativeSpec.toBase_app` with its second factor identified by
`Situation.universalAlgebraMap_app_eq_sectionsIso`. -/
theorem Situation.totalSpaceToBase_app_affine (U : D.X.affineOpens) :
    D.totalSpaceToBase.app U.1 =
      D.algebraSheaf.hom.hom.app (op U.1) ≫ (D.sectionsIso U).hom :=
  (Stacks.RelativeSpec.toBase_app D.relativeSpecSituation U.1).trans
    (congrArg (fun k => D.algebraSheaf.hom.hom.app (op U.1) ≫ k)
      (D.universalAlgebraMap_app_eq_sectionsIso U))

/-- **The identification of the functions on `π^{-1}U` with `Sym_{Γ(X, U)}(Γ(L, U))` carries the
structure map of the symmetric algebra to `π^♯`.** So the identification is one of
`Γ(X, U)`-algebras and not merely of rings: a function pulled back from the base is a constant
of the symmetric algebra. -/
theorem Situation.symSectionsRingEquiv_algebraMap (U : D.X.affineOpens) (r : Γ(D.X, U.1)) :
    D.symSectionsRingEquiv U
        (algebraMap Γ(D.X, U.1) (SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1)) r) =
      (D.totalSpaceToBase.app U.1).hom r :=
  (congrArg (D.sectionsIso U).hom.hom
      (Stacks.SymAlgSections.ungradedSymSectionsRingEquiv_algebraMap D.L U.2 r)).trans
    (congrArg
      (fun k : Γ(D.X, U.1) ⟶ Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U.1) => k.hom r)
      (D.totalSpaceToBase_app_affine U)).symm

/-- **The affine local model `π^{-1}U = Spec Γ(X, U)[T]` carries the constants of the
polynomial ring to the structure morphism of the total space**: for `r ∈ Γ(X, U)` the function
`C r` on `π^{-1}U` is the pullback `π^♯ r` of `r` along `π`.

This is the fact that makes the fibre coordinate a *coordinate*: the identification of
`Γ(𝕃, π^{-1}U)` with `Γ(X, U)[T]` is one of `Γ(X, U)`-algebras for the algebra structure that
`π` itself puts on the functions of the total space, so the affine Poincaré lemma
`PolynomialDeRham.quasiIso_incl` for `Γ(X, U) → Γ(X, U)[T]` is a statement about `π`. -/
theorem Situation.polynomialSectionsRingEquiv_C (U : D.X.affineOpens)
    (b : Module.Basis PUnit Γ(D.X, U.1) Γ(D.L, U.1)) (r : Γ(D.X, U.1)) :
    D.polynomialSectionsRingEquiv U b (Polynomial.C r) =
      (D.totalSpaceToBase.app U.1).hom r :=
  (congrArg (D.symSectionsRingEquiv U)
      (((D.polynomialAlgEquiv U b).symm.commutes r :
        (D.polynomialAlgEquiv U b).symm (Polynomial.C r) =
          algebraMap Γ(D.X, U.1) (SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1)) r))).trans
    (D.symSectionsRingEquiv_algebraMap U r)

end Stacks.LineBundle

end
