module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.BaseChangeDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.DegenerateConicBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ExceptionalComponentsMeet
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition

/-!
# A rational bridge whose base change is not a disjoint union of rational bridges

Let `k` be a field in which `-1` is not a square, `K` an extension in which it is — for instance
`ℝ ⊆ ℂ` — and let

```
X = V(T₂ · (T₀² + T₁²)) ⊆ 𝐏²_k ,     C = V(T₀² + T₁²) ⊆ X
```

be the union of a line and a degenerate conic, together with the conic component. Then `C` is a
rational bridge of `X` in the sense of `AlgebraicGeometry.IsRationalBridge`: it is integral
because `T₀² + T₁²` is irreducible over `k` ([Stacks, Tag 0BYC]), its global functions are `k`
and its genus is zero ([Stacks, Tag 0BYD]), it is an irreducible component of `X`, and the
closure of its complement is the line `V(T₂)`, which meets `C` in `Spec k[t]/(t² + 1)`, of degree
two over `k`. The base change `X_K` is the triangle of lines `T₂`, `T₀ + iT₁`, `T₀ - iT₁`, whose
three pairwise intersections are ordinary double points, so `X` has at-worst-nodal singularities
— [Stacks, Tag 0C47] tests nodality after base change to an algebraic closure, so a node whose
two branches are conjugate is a node.

The inverse image of `C` in `X_K` is the conic `V(T₀² + T₁²) ⊆ 𝐏²_K`, which is the union of the
two lines `T₀ ± iT₁`. Those two lines meet, at `[0 : 0 : 1]`, so the inverse image is connected,
while `T₀² + T₁² = (T₀ + iT₁)(T₀ - iT₁)` is reducible over `K`, so the inverse image is not
integral. A connected scheme that is not integral is not isomorphic to a coproduct of integral
schemes, and the first clause of `AlgebraicGeometry.IsRationalBridge` is integrality. So the
inverse image of `C` in `X_K` is not a finite *disjoint* union of rational bridges of `X_K`.

That is the conclusion [Stacks, Tag 0E65] asserts, and
`Stacks.Curves.DegenerateConic.not_exists_iso_sigma_isRationalBridge_degenerateConic` refutes it
in exactly the shape in which
`AlgebraicGeometry.exists_iso_sigma_isRationalBridge_baseChange` of
`Curves/ContractingRationalBridges/BaseChange.lean` proves it — that theorem's conclusion with
its extra hypothesis `hgeom` of geometric integrality deleted. The hypothesis is what carries
that proof, and `Stacks.Curves.DegenerateConic.not_geometricallyIntegral_toSpecΓ_conic` shows it
genuinely fails for this bridge, so the counterexample is not excluded by it. The repair at the
tag's own hypotheses drops the disjointness instead, and is
`AlgebraicGeometry.exists_finset_isRationalBridge_baseChange`, which carries the tag.

## Main results

* `AlgebraicGeometry.not_exists_iso_sigma_isRationalBridge_of_not_isIntegral`: a connected closed
  subscheme that is not integral is not a finite disjoint union of rational bridges. This is the
  mechanism of the refutation, and uses nothing about plane curves.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.connectedSpace_planeCurve`: a plane curve in the
  sense of [Stacks, Tag 0BYB] is connected, because its global functions are the constants
  ([Stacks, Tag 0BYD]) and [Stacks, Tag 0BY5] turns that into connectedness. Irreducibility is
  not assumed, and for the conic over `K` it is false.
* `Stacks.Curves.DegenerateConic.not_isIntegral_conic`: the degenerate conic over a field
  containing a square root of `-1` is not integral.
* `Stacks.Curves.DegenerateConic.not_geometricallyIntegral_toSpecΓ_conic`: the degenerate conic
  over `k` is not geometrically integral over its own field of global functions, which is the
  form the hypothesis `hgeom` takes.
* `Stacks.Curves.DegenerateConic.not_exists_iso_sigma_isRationalBridge_degenerateConic`: the
  refutation.

## Implementation notes

The witness is presented by the data that cuts it out rather than constructed: the ambient curve
is an arbitrary proper scheme `Y` over `K`, the inverse image of the bridge is an arbitrary ideal
sheaf `C` on `Y`, and the hypotheses say that `C` cuts out the plane curve of the equation
`T₀² + T₁²` over `K` — nonempty, without embedded points, equidimensional of dimension one, with
`I(C) = (T₀² + T₁²)`. These are the hypotheses of [Stacks, Tag 0BYB], the form in which
`StacksFrontier/AlgebraicGeometry/Curves/PlaneCurveGenus.lean` and
`StacksFrontier/AlgebraicGeometry/Curves/DegenerateConicBaseChange.lean` state everything about
plane curves, and they hold for `Y = X_K` and `C` the inverse image of the conic component. No
tag is registered on any statement here: the refutation is not a clause of [Stacks, Tag 0E65].

## References

* [Stacks Project, Tag 0E65](https://stacks.math.columbia.edu/tag/0E65)
* [Stacks Project, Tag 0BYB](https://stacks.math.columbia.edu/tag/0BYB)
* [Stacks Project, Tag 0BYC](https://stacks.math.columbia.edu/tag/0BYC)
* [Stacks Project, Tag 0BYD](https://stacks.math.columbia.edu/tag/0BYD)
* [Stacks Project, Tag 0BY5](https://stacks.math.columbia.edu/tag/0BY5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.AlgebraicGeometry.IdealOfClosedSubscheme (idealOfClosedSubscheme)

universe u

namespace AlgebraicGeometry

/-! ### Why a connected non-integral subscheme is not a disjoint union of bridges -/

/-- **A connected closed subscheme that is not integral is not a finite disjoint union of
rational bridges.**

A rational bridge is integral, hence irreducible and reduced. A coproduct of reduced schemes is
reduced, and a *connected* coproduct of integral schemes is irreducible
(`AlgebraicGeometry.irreducibleSpace_coproduct_of_connectedSpace`: only one summand can occur),
so a connected scheme isomorphic to such a coproduct is integral. The compatibility of the
isomorphism with the closed immersions into the ambient scheme is not used, and neither is the
finiteness of the index set.

This is the mechanism by which
`Stacks.Curves.DegenerateConic.not_exists_iso_sigma_isRationalBridge_degenerateConic` refutes the
disjoint-union conclusion of [Stacks, Tag 0E65]: over `k = ℝ` the inverse image in `X_ℂ` of the
conic component of `V(T₂(T₀² + T₁²))` is two lines meeting in a point, connected and not
integral. -/
theorem not_exists_iso_sigma_isRationalBridge_of_not_isIntegral
    (K : Type u) [Field K] (Y : Scheme.{u}) [Y.Over (Spec (.of K))]
    [IsProper (Y ↘ Spec (.of K))] (C : Y.IdealSheafData) [ConnectedSpace C.subscheme]
    (hC : ¬ IsIntegral C.subscheme) :
    ¬ ∃ (ι : Type u) (_ : Finite ι) (D : ι → Y.IdealSheafData)
        (_ : ∀ n, IsRationalBridge K Y (D n))
        (e : (∐ fun n ↦ (D n).subscheme) ≅ C.subscheme),
      e.hom ≫ C.subschemeι = Sigma.desc (fun n ↦ (D n).subschemeι) := by
  rintro ⟨ι, -, D, hD, e, -⟩
  have hint : ∀ n, IsIntegral (D n).subscheme := fun n ↦ (hD n).isIntegral
  have hredX : ∀ n, IsReduced ((sigmaOpenCover (fun n ↦ (D n).subscheme)).X n) := by
    intro n
    have := hint n
    exact inferInstanceAs (IsReduced (D n).subscheme)
  have hred : IsReduced (∐ fun n ↦ (D n).subscheme : Scheme.{u}) :=
    IsReduced.of_openCover _ (sigmaOpenCover _)
  have hconn : ConnectedSpace (∐ fun n ↦ (D n).subscheme : Scheme.{u}) :=
    e.symm.hom.homeomorph.connectedSpace_iff.mp inferInstance
  have hirr : IrreducibleSpace (∐ fun n ↦ (D n).subscheme : Scheme.{u}) :=
    irreducibleSpace_coproduct_of_connectedSpace _
  exact hC (ObjectProperty.prop_of_iso (AlgebraicGeometry.IsIntegral (X := ·)) e
    (isIntegral_of_irreducibleSpace_of_isReduced _))

/-! ### Plane curves are connected -/

namespace ProjectiveSpectrum.Proj

/-- **The constants are the whole of the global functions on a plane curve.** By
[Stacks, Tag 0BYD] the degree-zero cohomology of the structure sheaf of a plane curve is
one-dimensional over the base field (`planeCurveGlobalSectionsEquiv`), so the structure map
`k ⟶ Γ(Z, 𝒪_Z)` is an isomorphism: it is injective because `k` is a field, and surjective
because a one-dimensional algebra is spanned by `1`. Irreducibility of the equation is not
assumed. -/
theorem isIso_globalSections_planeCurve {k : Type u} [Field k] (C : PlaneCurveData k) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ C.toSpec.appTop) := by
  have hiC := C.isClosedImmersion
  obtain ⟨z⟩ := C.nonempty
  have hne : Nonempty ((⊤ : C.Z.Opens) : Type u) := ⟨⟨z, trivial⟩⟩
  have hnt : Nontrivial Γ(C.Z, ⊤) := inferInstance
  refine Stacks.Models.isIso_constants_of_finrank_globalSections_eq_one C.toSpec ?_
  rw [← finrank_structureSheafCohomology_zero_eq_finrank_globalSections k C.toSpec,
    (planeCurveGlobalSectionsEquiv C).finrank_eq, Module.finrank_self]

/-- **A plane curve is connected.** Its global functions are the constants
(`isIso_globalSections_planeCurve`), and a scheme over a field with only constant global
functions is connected by [Stacks, Tag 0BY5].

The hypotheses are those of [Stacks, Tag 0BYB] and do not include irreducibility of the equation:
the conic `V(T₀² + T₁²)` over a field containing a square root of `-1` is two distinct lines, and
this says that they meet. -/
theorem connectedSpace_planeCurve {k : Type u} [Field k] (C : PlaneCurveData k) :
    ConnectedSpace C.Z :=
  have := isIso_globalSections_planeCurve C
  connectedSpace_of_isIso_globalSections k C.toSpec

end ProjectiveSpectrum.Proj

end AlgebraicGeometry

namespace Stacks.Curves.DegenerateConic

open AlgebraicGeometry.ProjectiveSpectrum.Proj (connectedSpace_planeCurve
  isIso_globalSections_planeCurve projectivePlane_isVariety_of_isIntegral)

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The degenerate conic over a field containing a square root of `-1` -/

/-- **The degenerate conic over a field containing a square root of `-1` is not integral.**
It is a plane curve of dimension one, so were it integral it would be a curve over `K` — an
integral closed subscheme of `𝐏²_K` is a variety (`projectivePlane_isVariety_of_isIntegral`) —
and `not_isCurve_conic` says it is not, because `T₀² + T₁² = (T₀ + iT₁)(T₀ - iT₁)` is reducible
over `K`. -/
theorem not_isIntegral_conic {K : Type u} [Field K] (i : K) (hi : i ^ 2 = -1)
    {W : Scheme.{u}} [Nonempty W]
    (iW : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) K)) [IsClosedImmersion iW]
    (hdimW : ∀ V ∈ irreducibleComponents W, topologicalKrullDim V = 1)
    (hIW : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) K) iW =
      Ideal.span {conicForm K}) :
    ¬ IsIntegral W := fun _ =>
  not_isCurve_conic i hi iW hdimW hIW
    { toIsVariety := projectivePlane_isVariety_of_isIntegral K iW
      topologicalKrullDim_eq_one :=
        topologicalKrullDim_eq_one_of_forall_mem_irreducibleComponents hdimW }

/-- **The degenerate conic is not geometrically integral over its own field of global
functions.** This is the shape in which the hypothesis `hgeom` of
`AlgebraicGeometry.exists_iso_sigma_isRationalBridge_baseChange` is stated: geometric integrality
of the bridge relative to `Scheme.toSpecΓ`, not relative to the ground field.

The two readings agree here because the global functions of a plane curve are the constants
(`isIso_globalSections_planeCurve`): the structure morphism `Z ⟶ Spec k` factors as `Z.toSpecΓ`
followed by an isomorphism, and geometric integrality is invariant under composition with an
isomorphism. So `not_geometricallyIntegral_conic` applies, and the hypothesis that carries the
disjoint decomposition genuinely fails for this bridge. -/
theorem not_geometricallyIntegral_toSpecΓ_conic {k : Type u} [Field k] (hk : ∀ c : k, c ^ 2 ≠ -1)
    (K : Type u) [Field K] [Algebra k K] (i : K) (hi : i ^ 2 = -1)
    {Z : Scheme.{u}} [Nonempty Z]
    (iZ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion iZ]
    (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ V ∈ irreducibleComponents Z, topologicalKrullDim V = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) iZ =
      Ideal.span {conicForm k}) :
    ¬ GeometricallyIntegral Z.toSpecΓ := by
  intro hgi
  have : MorphismProperty.RespectsIso (@GeometricallyIntegral) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  set f : Z ⟶ Spec (.of k) := iZ ≫ projToSpecCoeff k 2 with hf
  have hconst : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_planeCurve (conicData iZ hno hdim hI)
  have : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv f.appTop
  have hcomp : GeometricallyIntegral (Z.toSpecΓ ≫ Spec.map f.appTop) :=
    (MorphismProperty.cancel_right_of_respectsIso (@GeometricallyIntegral) Z.toSpecΓ
      (Spec.map f.appTop)).mpr hgi
  rw [← Scheme.toSpecΓ_naturality f] at hcomp
  exact not_geometricallyIntegral_conic hk K i hi iZ hI
    ((MorphismProperty.cancel_right_of_respectsIso (@GeometricallyIntegral) f
      (Spec (.of k)).toSpecΓ).mp hcomp)

/-! ### The refutation -/

/-- **The base change of a rational bridge need not be a finite disjoint union of rational
bridges**, so the conclusion of [Stacks, Tag 0E65] is false as stated.

Let `K` be a field containing a square root `i` of `-1`, let `Y` be a proper scheme over `K`, and
let `C ⊆ Y` be a closed subscheme cut out, inside some projective plane over `K`, by the
degenerate conic `T₀² + T₁²` — nonempty, without embedded points and equidimensional of dimension
one, which are the hypotheses of [Stacks, Tag 0BYB]. Then there is no finite family of rational
bridges of `Y` whose coproduct is isomorphic to `C` over `Y`.

**What this refutes.** Taking `K = ℂ`, `Y = X_ℂ` for `X = V(T₂(T₀² + T₁²)) ⊆ 𝐏²_ℝ`, and `C` the
inverse image in `X_ℂ` of the rational bridge `V(T₀² + T₁²) ⊆ X`, the statement denied here is
precisely the conclusion of `AlgebraicGeometry.exists_iso_sigma_isRationalBridge_baseChange` with
its hypothesis `hgeom` of geometric integrality deleted — that is, the conclusion
[Stacks, Tag 0E65] asserts at its own hypotheses. The module docstring above checks that `X` and
`C` satisfy them: `X` is proper of dimension one over `ℝ` with `H⁰(X, 𝒪_X) = ℝ` and at-worst-nodal
singularities, and `C` is integral of genus zero, an irreducible component of `X`, meeting the
closure of its complement in degree two. The hypothesis `hgeom` is not a way out, by
`not_geometricallyIntegral_toSpecΓ_conic`; and `AlgebraicGeometry.IsRationalBridge` is not at
fault either, since the two lines of `C_ℂ` are each a rational bridge of `X_ℂ` — what fails is
only that they are not disjoint, which is why
`AlgebraicGeometry.exists_finset_isRationalBridge_baseChange` repairs the tag by asking for the
scheme-theoretic union instead.

**Why it fails.** The field `k' = H⁰(C, 𝒪_C)` of the bridge is `ℝ`, so `k' ⊗_ℝ ℂ = ℂ` is a single
factor and the decomposition the source writes down has one piece, namely `C_ℂ` itself. That
piece is the pair of lines `T₀ ± iT₁`, which is connected — plane curves are connected, by
`connectedSpace_planeCurve` — and reducible, hence not integral, by `not_isIntegral_conic`; and
integrality is the first clause of `AlgebraicGeometry.IsRationalBridge`. So no decomposition into
rational bridges exists at all, disjoint or otherwise, with one piece or with many:
`AlgebraicGeometry.not_exists_iso_sigma_isRationalBridge_of_not_isIntegral` rules them all out at
once. -/
theorem not_exists_iso_sigma_isRationalBridge_degenerateConic
    {K : Type u} [Field K] (i : K) (hi : i ^ 2 = -1)
    (Y : Scheme.{u}) [Y.Over (Spec (.of K))] [IsProper (Y ↘ Spec (.of K))]
    (C : Y.IdealSheafData) [Nonempty C.subscheme]
    (iC : C.subscheme ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    [IsClosedImmersion iC]
    (hno : HasNoEmbeddedPoints C.subscheme)
    (hdim : ∀ V ∈ irreducibleComponents C.subscheme, topologicalKrullDim V = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) K) iC =
      Ideal.span {conicForm K}) :
    ¬ ∃ (ι : Type u) (_ : Finite ι) (D : ι → Y.IdealSheafData)
        (_ : ∀ n, IsRationalBridge K Y (D n))
        (e : (∐ fun n ↦ (D n).subscheme) ≅ C.subscheme),
      e.hom ≫ C.subschemeι = Sigma.desc (fun n ↦ (D n).subschemeι) :=
  have : ConnectedSpace C.subscheme := connectedSpace_planeCurve (conicData iC hno hdim hI)
  not_exists_iso_sigma_isRationalBridge_of_not_isIntegral K Y C
    (not_isIntegral_conic i hi iC hdim hI)

end Stacks.Curves.DegenerateConic

end
