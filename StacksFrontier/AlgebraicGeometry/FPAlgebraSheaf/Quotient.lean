module

public import StacksFrontier.AlgebraicGeometry.FPAlgebraSheaf.Polynomial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quotients of algebra sheaves by quasi-coherent ideals, and `Sym(F)/I`

Two further families of finitely presented quasi-coherent `𝒪_X`-algebras are constructed, both
by the direct image of `Stacks.FPAlgebraSheaf.isOfFinitePresentation_pushforwardAlgebra`:

* `𝒪_X / I` for `I` a quasi-coherent ideal, i.e. `I : X.IdealSheafData`;
* `𝒪_X[x_i] / I` for `I` a quasi-coherent ideal of the polynomial algebra sheaf, which is the
  `Sym(F)/I` shape the directed system of [Stacks, Tag 05JS] is built from.

A quotient of a sheaf of rings by a sheaf of ideals is not a sheaf -- the quotient presheaf
fails glueing -- so the quotient algebra sheaf cannot be formed by taking quotients sectionwise.
Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData` constructs the *closed subscheme* cut out by
a quasi-coherent ideal, by glueing, and so lands in `Over X`; it never passes through
`Under X.sheaf`.  The bridge taken here is that the direct image of the structure sheaf of that
closed subscheme *is* the quotient algebra sheaf, and is an object of `Under X.sheaf` by
construction, since a direct image of a sheaf is a sheaf.

With the quotient available, the general statement needs no new idea: a closed subscheme of a
scheme affine and of finite presentation over `X` is again affine over `X`, and its structural
ring map over an affine open factors as a finitely presented map followed by a surjection with
finitely generated kernel.  Taking the ambient scheme to be affine `n`-space gives `Sym(F)/I`
for a free `F` of finite rank.

## Main definitions

* `Stacks.FPAlgebraSheaf.quotientAlgebra I`: **`𝒪_X / I` as an object of
  `AlgebraicGeometry.Scheme.QuasicoherentAlgebra X`.**
* `Stacks.FPAlgebraSheaf.polynomialQuotientAlgebra X n I`: **`𝒪_X[x_i] / I`, `i : n`, as an
  object of `AlgebraicGeometry.Scheme.QuasicoherentAlgebra X`.**

## Main results

* `Stacks.FPAlgebraSheaf.isOfFinitePresentation_quotientAlgebra`: **`𝒪_X / I` is of finite
  presentation when `I` is finitely generated over every affine open.**
* `Stacks.FPAlgebraSheaf.isOfFinitePresentation_pushforwardAlgebra_subschemeι_comp`: the general
  statement, for a closed subscheme of any scheme affine and locally of finite presentation
  over `X`.
* `Stacks.FPAlgebraSheaf.isOfFinitePresentation_polynomialQuotientAlgebra`: **`𝒪_X[x_i] / I` is
  a quasi-coherent algebra of finite presentation for `n` finite and `I` finitely generated over
  every affine open**, which is the shape of the members of the directed system of
  [Stacks, Tag 05JS].

## Implementation notes

Over an affine open `U` of `X` the structural ring map of `𝒪_X / I` is
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι.app U`, which Mathlib knows to be surjective
with kernel `I.ideal U`.  Finite presentation is then
`RingHom.FinitePresentation.of_surjective`, and the hypothesis `(I.ideal U).FG` is exactly the
condition that `I` be of finite type.  Affineness of the preimage is not used for this: the
kernel statement holds over an affine open of `X` whatever the preimage looks like.  It is used
only for quasi-coherence, where it comes from the closed immersion being an affine morphism.

The factorisation in the general statement is `Scheme.Hom.comp_app`, which is `rfl`, so the
composite's structural ring map is literally the composite of the two, and
`RingHom.FinitePresentation.comp` finishes.  Nothing is transported.

## What is not done

`polynomialQuotientAlgebra` is not identified with a quotient of `MvPolynomial`: the sections of
`polynomialAlgebra X n` over an affine open are not identified with a polynomial ring in the
first place (see the corresponding note in
`StacksFrontier.AlgebraicGeometry.FPAlgebraSheaf.Polynomial`), so the quotient is not identified
with a quotient of one either.  What is proved is that the object is a quasi-coherent algebra of
finite presentation, which is what [Stacks, Tag 05JS] asks of the members of its system.

Also not proved is that every finitely presented quasi-coherent algebra is of this form.  That
is the surjectivity half of [Stacks, Tag 05JS]'s construction and needs the sections
identification above together with a choice of generators and relations.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.FPAlgebraSheaf

variable {X : Scheme.{u}}

/-! ### The quotient of the structure sheaf by a quasi-coherent ideal -/

/-- **`𝒪_X / I`**, the quotient of the structure sheaf by a quasi-coherent ideal, as a sheaf of
commutative `𝒪_X`-algebras: the direct image of the structure sheaf of the closed subscheme cut
out by `I`.  A direct image of a sheaf is a sheaf, so no quotient presheaf has to be
sheafified. -/
def quotientAlgebra (I : X.IdealSheafData) : X.QuasicoherentAlgebra :=
  pushforwardAlgebra I.subschemeι

/-- The structural ring map of `𝒪_X / I` over an open `U` is the map on sections induced by the
closed immersion of the subscheme cut out by `I`. -/
theorem hom_app_quotientAlgebra (I : X.IdealSheafData) (U : X.Opens) :
    (quotientAlgebra I).hom.hom.app (op U) = I.subschemeι.app U :=
  rfl

/-- **`𝒪_X / I` is quasi-coherent.**  A closed immersion is an affine morphism, and a direct
image of the structure sheaf along an affine morphism is a quasi-coherent algebra. -/
theorem isQuasicoherent_quotientAlgebra (I : X.IdealSheafData) :
    Scheme.QuasicoherentAlgebra.IsQuasicoherent (quotientAlgebra I) :=
  isQuasicoherent_pushforwardAlgebra _

/-- The map on sections over an affine open induced by the closed immersion of the subscheme cut
out by a finitely generated ideal is of finite presentation. -/
private theorem finitePresentation_subschemeι_app {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (hI : ∀ V : Y.affineOpens, (I.ideal V).FG) (V : Y.affineOpens) :
    RingHom.FinitePresentation (I.subschemeι.app V).hom := by
  refine RingHom.FinitePresentation.of_surjective _ (I.subschemeι_app_surjective V) ?_
  rw [I.ker_subschemeι_app V]
  exact hI V

/-- **`𝒪_X / I` is of finite presentation when `I` is finitely generated over every affine
open.**  Over an affine open the structural ring map is the quotient map by `I.ideal U`, which is
surjective with kernel `I.ideal U`. -/
theorem isOfFinitePresentation_quotientAlgebra (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).FG) :
    Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (quotientAlgebra I) := by
  intro U hU
  exact finitePresentation_subschemeι_app I hI ⟨U, hU⟩

/-- **`𝒪_X / I` satisfies both conditions imposed on the members of the directed system of
[Stacks, Tag 05JS]** when `I` is finitely generated over every affine open. -/
theorem isQuasicoherent_and_isOfFinitePresentation_quotientAlgebra (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).FG) :
    Scheme.QuasicoherentAlgebra.IsQuasicoherent (quotientAlgebra I) ∧
      Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (quotientAlgebra I) :=
  ⟨isQuasicoherent_quotientAlgebra I, isOfFinitePresentation_quotientAlgebra I hI⟩

/-! ### Quotients of an arbitrary finitely presented algebra sheaf -/

/-- **A closed subscheme, cut out by a finitely generated ideal, of a scheme affine and locally
of finite presentation over `X`, gives a finitely presented algebra sheaf on `X`.**  Over an
affine open `U` of `X` the structural ring map factors as the finitely presented map
`Γ(X, U) ⟶ Γ(Y, f ⁻¹ᵁ U)` followed by the quotient by `I.ideal (f ⁻¹ᵁ U)`, which is surjective
with finitely generated kernel. -/
@[ega "IV 8.6.1" "direction"]
theorem isOfFinitePresentation_pushforwardAlgebra_subschemeι_comp {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] [LocallyOfFinitePresentation f] (I : Y.IdealSheafData)
    (hI : ∀ V : Y.affineOpens, (I.ideal V).FG) :
    Scheme.QuasicoherentAlgebra.IsOfFinitePresentation
      (pushforwardAlgebra (I.subschemeι ≫ f)) := by
  intro U hU
  show RingHom.FinitePresentation ((I.subschemeι ≫ f).app U).hom
  have hbase : RingHom.FinitePresentation (f.app U).hom := by
    have h := LocallyOfFinitePresentation.finitePresentation_appLE f hU (hU.preimage f) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at h
  exact (finitePresentation_subschemeι_app I hI ⟨f ⁻¹ᵁ U, hU.preimage f⟩).comp hbase

/-- Such a closed subscheme is affine over `X`, so its direct image is quasi-coherent. -/
theorem isQuasicoherent_pushforwardAlgebra_subschemeι_comp {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] (I : Y.IdealSheafData) :
    Scheme.QuasicoherentAlgebra.IsQuasicoherent (pushforwardAlgebra (I.subschemeι ≫ f)) :=
  isQuasicoherent_pushforwardAlgebra _

/-! ### `Sym(F)/I` for `F` free of finite rank -/

/-- **`𝒪_X[x_i] / I`, `i : n`**, for `I` a quasi-coherent ideal of the polynomial algebra sheaf:
the direct image of the structure sheaf of the closed subscheme of affine `n`-space cut out by
`I`.  For `n` finite this is `Sym(F)/I` with `F` free of rank `n`, which is the shape of the
members of the directed system of [Stacks, Tag 05JS]. -/
def polynomialQuotientAlgebra (X : Scheme.{u}) (n : Type u)
    (I : (𝔸(n; X)).IdealSheafData) : X.QuasicoherentAlgebra :=
  pushforwardAlgebra (I.subschemeι ≫ 𝔸(n; X) ↘ X)

/-- **`𝒪_X[x_i] / I` is quasi-coherent.** -/
theorem isQuasicoherent_polynomialQuotientAlgebra (X : Scheme.{u}) (n : Type u)
    (I : (𝔸(n; X)).IdealSheafData) :
    Scheme.QuasicoherentAlgebra.IsQuasicoherent (polynomialQuotientAlgebra X n I) :=
  isQuasicoherent_pushforwardAlgebra_subschemeι_comp _ I

/-- **`𝒪_X[x_i] / I` is of finite presentation** for finitely many variables and `I` finitely
generated over every affine open of affine `n`-space: an algebra sheaf of the shape `Sym(F)/I`
that [Stacks, Tag 05JS] needs. -/
theorem isOfFinitePresentation_polynomialQuotientAlgebra (X : Scheme.{u}) (n : Type u)
    [Finite n] (I : (𝔸(n; X)).IdealSheafData)
    (hI : ∀ V : (𝔸(n; X)).affineOpens, (I.ideal V).FG) :
    Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (polynomialQuotientAlgebra X n I) :=
  isOfFinitePresentation_pushforwardAlgebra_subschemeι_comp _ I hI

/-- **`𝒪_X[x_i] / I` satisfies both conditions imposed on the members of the directed system of
[Stacks, Tag 05JS].** -/
theorem isQuasicoherent_and_isOfFinitePresentation_polynomialQuotientAlgebra
    (X : Scheme.{u}) (n : Type u) [Finite n] (I : (𝔸(n; X)).IdealSheafData)
    (hI : ∀ V : (𝔸(n; X)).affineOpens, (I.ideal V).FG) :
    Scheme.QuasicoherentAlgebra.IsQuasicoherent (polynomialQuotientAlgebra X n I) ∧
      Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (polynomialQuotientAlgebra X n I) :=
  ⟨isQuasicoherent_polynomialQuotientAlgebra X n I,
    isOfFinitePresentation_polynomialQuotientAlgebra X n I hI⟩

end Stacks.FPAlgebraSheaf
