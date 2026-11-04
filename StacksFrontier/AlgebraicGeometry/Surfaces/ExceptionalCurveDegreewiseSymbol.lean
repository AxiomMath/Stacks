module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.DegreewiseSymbolPresentation
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhood
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistSectionsTransport
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodGradedPieceSections
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhoodSupplement

/-!
# The degreewise symbol system of an exceptional curve of the first kind

Let `X` be a Noetherian scheme, let `E ⊂ X` be an exceptional curve of the first kind cut out by
an ideal sheaf `D` and presented as the projective line by `e : 𝐏¹_k ≅ E`, and let
`A = AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing D` be the ring of compatible
global functions on the infinitesimal thickenings of `E`, filtered by the projection kernels
`Iₙ₊₁ = ker (A ⟶ Γ(Eₙ₊₁, 𝒪))`.

This file assembles a
`AlgebraicGeometry.SemistableReduction.DegreewiseSymbol` on that filtration out of the pieces
already in the development, and so reduces all five geometric inputs of [Stacks, Tag 0C2K] to
the single statement

`Iₙ₊₁ ⊆ I₁ Iₙ + Iₙ₊₂`,

that the associated graded ring is generated in degree one.

## What is assembled

`AlgebraicGeometry.SemistableReduction.DegreewiseSymbol.ofGradedPresentation` builds the symbol
system from a residue homomorphism `A ⟶ k` with kernel `I₁` and a family of `k`-vector spaces
`Wₙ` of dimension `n + 1` presenting `Iₙ / Iₙ₊₁`. Both are produced here.

* The residue homomorphism is
  `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodScalar`: projection to the first
  thickening, restricted to `E` along `D ^ 1 ≤ D`, and read as a coefficient by
  `AlgebraicGeometry.Scheme.IdealSheafData.sectionsSubschemeRingEquivOfIso`. Restricting along
  `D ^ 1 ≤ D` rather than transporting along `pow_one` keeps the map a composite of ring
  homomorphisms, with no cast; the restriction is invertible because `inclusion` of an equality
  of ideal sheaves is, by `AlgebraicGeometry.Scheme.IdealSheafData.inclusion_comp` and
  `inclusion_id`. Its kernel is `I₁` on the nose and it is onto for an exceptional curve, since
  the projections out of `A` are.
* The spaces are `Wₙ = Γ(X, 𝒪_X(-D ^ n)|_D)`, of dimension `n + 1` by
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.finrank_restrictedNegativeTwistSections`.
* The presentations `σₙ` are the 0C4T injection
  `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom` read backwards. That map is an
  injective additive `ψₙ` from `Wₙ₊₁` onto the projections of `Iₙ₊₁`, with zero fibre `Iₙ₊₂` and
  with `ψₙ (ū · x) = u · ψₙ x`; `σₙ₊₁` is its inverse on that image, `Function.invFun`, and each
  of its four properties is read off `ψₙ`'s by injectivity. It is a named construction, not an
  `Exists.choose`, so the injections in two different degrees may appear in one statement — which
  is what any proof of degree-one generation has to do.

The `n = 0` slot is separate, because the 0C4T sequence starts the graded pieces at `I₁ / I₂`:
`I₀ / I₁` is the residue field itself, so `σ₀` is the residue homomorphism followed by any
`k`-linear isomorphism `k ≅ W₀` — one exists because `W₀` has dimension `1`, and which one is
chosen is immaterial for exactly the reason recorded in the module docstring of
`StacksFrontier/AlgebraicGeometry/SemistableReduction/DegreewiseSymbol.lean`.

The semilinearity of `σₙ` is where the two scalar actions meet. On `Wₙ` the `k`-action is
restriction of scalars along `sectionsSubschemeRingEquivOfIso`, while `ψₙ` is semilinear for
`Γ(E, 𝒪_E)`; the bridge is that the residue of `c` and the restriction to `E` of its projection
to *any* thickening agree, which is
`AlgebraicGeometry.Scheme.IdealSheafData.symm_formalNeighborhoodScalar` — the inverse limit read
through `thickeningRestrictionLE_formalNeighborhoodProjection`.

## What degree-one generation needed, and where it is

Degree-one generation `Iₙ₊₁ ⊆ I₁ Iₙ + Iₙ₊₂` is not a consequence of the data assembled here: a
degreewise symbol system constrains each graded piece separately and says nothing about products,
so the associated graded ring is pinned only up to its Hilbert function. It is the one remaining
input of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofExceptionalCurve`, and it is
proved in
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistMultiplicative.lean` and
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveMonomialData.lean`. Nothing here carries
a `@[stacks]` attribute: Tag 0C2K asserts the structure of `A`, not this step of its proof.

All four of the things degree-one generation needs are now in the development.

* The injections `ψₙ` in different degrees are values of one construction,
  `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom`, so a statement relating two of
  them is possible.
* The spaces `Wₘ` they come from carry a multiplication across the degrees,
  `Stacks.Divisors.restrictedIdealMulSections`, since `i^*ℐ_I ⊗ i^*ℐ_J ≅ i^*ℐ_{I · J}` by
  `Stacks.Divisors.restrictedIdealTensorMulIso`.
* **The two agree**: for `a ∈ Iₘ` and `b ∈ Iₙ` the symbol of `a b` is the product of the
  symbols, by
  `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections` in
  `StacksFrontier/AlgebraicGeometry/Surfaces/GradedSectionsLocal.lean`, which also places the
  restricted products in
  `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsDegreeOneProducts`.
* **The comparison with the twists of `𝐏¹` is made multiplicative** in
  `StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistMultiplicative.lean`. The
  per-degree choices `Wₘ ≅ H⁰(𝐏¹_k, 𝒪(m))` of
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf` relate no two degrees and are not made
  compatible; instead the comparison in the degree of a *product* is assembled out of the two
  factors' choices, through Tag 01CD and Equation 01MO, and is multiplicative by construction.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningResidue` — restriction of a global function
  on a thickening to `E`.
* `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodScalar` — the residue
  homomorphism `A ⟶ k`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.gradedSymbol` — the
  family of presentations of the graded pieces.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.degreewiseSymbol` —
  **the degreewise symbol system on the projection-kernel filtration.**

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.ker_formalNeighborhoodScalar` — the residue
  homomorphism has kernel `I₁`.
* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofExceptionalCurve` — **the
  five geometric inputs of [Stacks, Tag 0C2K] from degree-one generation alone.**

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-! ### Restriction of a function on a thickening to the exceptional curve -/

/-- Restricting along `I ≤ J` and then along `J ≤ K` is restricting along `I ≤ K`. -/
private theorem appTop_inclusion_appTop {I J K : X.IdealSheafData} (h₁ : I ≤ J) (h₂ : J ≤ K)
    (x : Γ(I.subscheme, ⊤)) :
    (inclusion h₂).appTop.hom ((inclusion h₁).appTop.hom x) =
      (inclusion (h₁.trans h₂)).appTop.hom x := by
  rw [← inclusion_comp h₁ h₂, Scheme.Hom.comp_appTop]
  rfl

/-- Restriction of a global function on the `(n + 1)`-st infinitesimal thickening of `D` to the
subscheme `E` cut out by `D` itself, induced by the inclusion `D ^ (n + 1) ≤ D` of ideal
sheaves. -/
public def thickeningResidue (n : ℕ) : Γ(thickening D n, ⊤) →+* Γ(D.subscheme, ⊤) :=
  (inclusion (pow_succ_le_self D n)).appTop.hom

/-- Restricting to `E` after restricting between thickenings restricts to `E`. -/
public theorem thickeningResidue_thickeningRestrictionLE {i j : ℕ} (h : i ≤ j)
    (x : Γ(thickening D j, ⊤)) :
    thickeningResidue D i (thickeningRestrictionLE D h x) = thickeningResidue D j x :=
  appTop_inclusion_appTop (pow_succ_le_pow_succ D h) (pow_succ_le_self D i) x

/-- **Every projection of a compatible function has the same restriction to `E`.** The value of a
compatible function on `E` does not depend on which thickening it is read off. -/
public theorem thickeningResidue_formalNeighborhoodProjection (n : ℕ)
    (a : formalNeighborhoodRing D) :
    thickeningResidue D n (formalNeighborhoodProjection D n a) =
      thickeningResidue D 0 (formalNeighborhoodProjection D 0 a) := by
  rw [← thickeningRestrictionLE_formalNeighborhoodProjection D (Nat.zero_le n) a,
    thickeningResidue_thickeningRestrictionLE]

/-- Restriction from the first thickening to `E` is injective: the inclusion
`E ⟶ (D ^ 1).subscheme` is an isomorphism, with inverse the inclusion going the other way, by
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion_comp` and `inclusion_id`. -/
public theorem thickeningResidue_zero_injective :
    Function.Injective (thickeningResidue D 0) :=
  Function.LeftInverse.injective
    (g := (inclusion (le_of_eq (pow_one D).symm)).appTop.hom) fun z => by
      rw [thickeningResidue, appTop_inclusion_appTop, inclusion_id]
      rfl

/-- Restriction from the first thickening to `E` is onto, for the same reason. -/
public theorem thickeningResidue_zero_surjective :
    Function.Surjective (thickeningResidue D 0) := fun y =>
  ⟨(inclusion (le_of_eq (pow_one D).symm)).appTop.hom y, by
    rw [thickeningResidue, appTop_inclusion_appTop, inclusion_id]
    rfl⟩

/-! ### The residue homomorphism -/

variable (k : Type u) [Field k]

/-- **The residue homomorphism `A ⟶ k`.** Project a compatible function to the first
infinitesimal thickening, restrict it to `E`, and read the result as a coefficient by
`AlgebraicGeometry.Scheme.IdealSheafData.sectionsSubschemeRingEquivOfIso`. This is the `scalar`
input of `AlgebraicGeometry.SemistableReduction.DegreewiseSymbol.ofGradedPresentation`. -/
public def formalNeighborhoodScalar (e : projectiveLineProj k ≅ D.subscheme) :
    formalNeighborhoodRing D →+* k :=
  (sectionsSubschemeRingEquivOfIso D k e).toRingHom.comp
    ((thickeningResidue D 0).comp (formalNeighborhoodProjection D 0))

@[simp]
public theorem formalNeighborhoodScalar_apply (e : projectiveLineProj k ≅ D.subscheme)
    (a : formalNeighborhoodRing D) :
    formalNeighborhoodScalar D k e a =
      sectionsSubschemeRingEquivOfIso D k e
        (thickeningResidue D 0 (formalNeighborhoodProjection D 0 a)) := rfl

/-- **The residue homomorphism has kernel the first step of the filtration.** Both the
coefficient reading and the restriction to `E` are injective, so the kernel is that of the
projection to the first thickening, which is `I₁` by definition. This is the `ker_scalar` input
of `AlgebraicGeometry.SemistableReduction.DegreewiseSymbol.ofGradedPresentation`. -/
public theorem ker_formalNeighborhoodScalar (e : projectiveLineProj k ≅ D.subscheme) :
    RingHom.ker (formalNeighborhoodScalar D k e) = formalNeighborhoodFiltration D 1 := by
  ext a
  rw [RingHom.mem_ker, formalNeighborhoodScalar_apply,
    formalNeighborhoodFiltration_succ, RingHom.mem_ker,
    ← map_zero (sectionsSubschemeRingEquivOfIso D k e),
    (sectionsSubschemeRingEquivOfIso D k e).injective.eq_iff,
    ← map_zero (thickeningResidue D 0)]
  exact (thickeningResidue_zero_injective D).eq_iff

/-- **The residue of a compatible function is the restriction to `E` of any of its
projections.** This is the bridge between the two scalar actions on the graded pieces: the
`k`-action on `Γ(X, 𝒪_X(-D ^ n)|_D)` is restriction of scalars along
`AlgebraicGeometry.Scheme.IdealSheafData.sectionsSubschemeRingEquivOfIso`, while the 0C4T
injection is semilinear for the global functions on `E` reached from the `(n + 1)`-st
thickening. -/
public theorem symm_formalNeighborhoodScalar (e : projectiveLineProj k ≅ D.subscheme)
    (a : formalNeighborhoodRing D) (n : ℕ) :
    (sectionsSubschemeRingEquivOfIso D k e).symm (formalNeighborhoodScalar D k e a) =
      thickeningResidue D n (formalNeighborhoodProjection D n a) := by
  rw [formalNeighborhoodScalar_apply, RingEquiv.symm_apply_apply]
  exact (thickeningResidue_formalNeighborhoodProjection D n a).symm

variable {D k} {e : projectiveLineProj k ≅ D.subscheme}

namespace IsExceptionalCurveOfFirstKind

/-- **The residue homomorphism is onto, for an exceptional curve of the first kind.** The
projections out of `A` are onto by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.surjective_formalNeighborhoodProjection`, and the other two factors are bijective. This is the
`surjective_scalar` input of
`AlgebraicGeometry.SemistableReduction.DegreewiseSymbol.ofGradedPresentation`. -/
public theorem surjective_formalNeighborhoodScalar (hE : IsExceptionalCurveOfFirstKind D k e) :
    Function.Surjective (formalNeighborhoodScalar D k e) :=
  (sectionsSubschemeRingEquivOfIso D k e).surjective.comp
    ((thickeningResidue_zero_surjective D).comp
      (hE.surjective_formalNeighborhoodProjection 0))

/-! ### The zeroth graded piece -/

/-- A `k`-linear isomorphism of `k` with `Γ(X, 𝒪_X(-D ^ 0)|_D)`, which has dimension `1` by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.finrank_restrictedNegativeTwistSections`. The isomorphism is a choice and nothing below
depends on which one is made: a degreewise symbol system relates the symbols in different
degrees in no way at all. -/
public def residueEquivZero (hE : IsExceptionalCurveOfFirstKind D k e) :
    k ≃ₗ[k] restrictedNegativeTwistSections D k e 0 :=
  haveI : FiniteDimensional k (restrictedNegativeTwistSections D k e 0) :=
    .of_finrank_pos (by rw [hE.finrank_restrictedNegativeTwistSections 0]; omega)
  LinearEquiv.ofFinrankEq _ _ (by
    rw [hE.finrank_restrictedNegativeTwistSections 0, Module.finrank_self])

/-! ### The 0C4T injection, named -/

/-- The 0C4T injection of the graded piece `Iₙ₊₁ / Iₙ₊₂` into the global functions on the
`(n + 2)`-nd thickening. It is the **named** map
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom`, not a choice: the injections in two
different degrees are values of one construction, so a statement relating them is possible at
all. -/
public def gradedPsi (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ) :
    Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
        (⊤ : D.subscheme.Opens)) →+ Γ(thickening D (n + 1), ⊤) :=
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1
  gradedSectionsHom D n

public theorem gradedPsi_injective (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ) :
    Function.Injective (gradedPsi hE n) :=
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1
  gradedSectionsHom_injective D n

/-- Every section of `𝒪_X(-D ^ (n + 1))|_D` is the projection of an element of `Iₙ₊₁`. -/
public theorem exists_mem_gradedPsi (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ) (x) :
    ∃ a ∈ formalNeighborhoodFiltration D (n + 1),
      formalNeighborhoodProjection D (n + 1) a = gradedPsi hE n x :=
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1
  exists_mem_gradedSectionsHom hE n x

/-- Every element of `Iₙ₊₁` projects to a section of `𝒪_X(-D ^ (n + 1))|_D`. -/
public theorem exists_gradedPsi_eq (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ)
    {a : formalNeighborhoodRing D} (ha : a ∈ formalNeighborhoodFiltration D (n + 1)) :
    ∃ x, gradedPsi hE n x = formalNeighborhoodProjection D (n + 1) a :=
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1
  exists_gradedSectionsHom_eq n ha

/-- An element of `Iₙ₊₁` lies in `Iₙ₊₂` exactly when the section it projects to vanishes. -/
public theorem mem_succ_iff_gradedPsi (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ) (x)
    {a : formalNeighborhoodRing D}
    (hax : formalNeighborhoodProjection D (n + 1) a = gradedPsi hE n x) :
    a ∈ formalNeighborhoodFiltration D (n + 2) ↔ x = 0 :=
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1
  mem_succ_iff_gradedSectionsHom n x hax

/-- The 0C4T injection is semilinear for the global functions on `E`. -/
public theorem gradedPsi_smul (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ)
    (u : Γ(thickening D (n + 1), ⊤)) (x) :
    gradedPsi hE n (thickeningResidue D (n + 1) u • x) = u * gradedPsi hE n x :=
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1
  gradedSectionsHom_smul D n u x

/-- **The 0C4T injection is semilinear over the residue homomorphism.** The `k`-action on
`Γ(X, 𝒪_X(-D ^ (n + 1))|_D)` is restriction of scalars along
`AlgebraicGeometry.Scheme.IdealSheafData.sectionsSubschemeRingEquivOfIso`, so the scalar `ū` of
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.gradedPsi_smul` at
`u = `the `(n + 1)`-st projection of `c` is the residue of `c`, by
`AlgebraicGeometry.Scheme.IdealSheafData.symm_formalNeighborhoodScalar`. -/
public theorem gradedPsi_smul_scalar (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ)
    (c : formalNeighborhoodRing D) (y : restrictedNegativeTwistSections D k e (n + 1)) :
    gradedPsi hE n (formalNeighborhoodScalar D k e c • y) =
      formalNeighborhoodProjection D (n + 1) c * gradedPsi hE n y := by
  have h2 := gradedPsi_smul hE n (formalNeighborhoodProjection D (n + 1) c)
    (@id Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens)) y)
  rwa [← symm_formalNeighborhoodScalar D k e c (n + 1)] at h2

/-! ### The symbol family -/

/-- **The family of presentations of the graded pieces.** In degree `n + 1` it is the inverse of
the 0C4T injection on its image — the section of `𝒪_X(-D ^ (n + 1))|_D` that a given element of
`Iₙ₊₁` projects to. In degree `0` the 0C4T sequence says nothing, since the graded pieces it
describes start at `I₁ / I₂`; there `I₀ / I₁` is the residue field, so the symbol is the residue
homomorphism followed by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.residueEquivZero`. -/
public def gradedSymbol (hE : IsExceptionalCurveOfFirstKind D k e) :
    ∀ n, formalNeighborhoodRing D → restrictedNegativeTwistSections D k e n
  | 0 => fun a => residueEquivZero hE (formalNeighborhoodScalar D k e a)
  | n + 1 => fun a =>
      Function.invFun (gradedPsi hE n) (formalNeighborhoodProjection D (n + 1) a)

public theorem gradedSymbol_zero_apply (hE : IsExceptionalCurveOfFirstKind D k e)
    (a : formalNeighborhoodRing D) :
    gradedSymbol hE 0 a = residueEquivZero hE (formalNeighborhoodScalar D k e a) := rfl

/-- **The symbol of an element of `Iₙ₊₁` is the section it projects to.** -/
public theorem gradedPsi_gradedSymbol (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ)
    {a : formalNeighborhoodRing D} (ha : a ∈ formalNeighborhoodFiltration D (n + 1)) :
    gradedPsi hE n (gradedSymbol hE (n + 1) a) = formalNeighborhoodProjection D (n + 1) a :=
  Function.invFun_eq (exists_gradedPsi_eq hE n ha)

/-- The symbol is additive on each step of the filtration. -/
public theorem gradedSymbol_add (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ)
    {a b : formalNeighborhoodRing D} (ha : a ∈ formalNeighborhoodFiltration D n)
    (hb : b ∈ formalNeighborhoodFiltration D n) :
    gradedSymbol hE n (a + b) = gradedSymbol hE n a + gradedSymbol hE n b := by
  cases n with
  | zero => simp only [gradedSymbol_zero_apply, map_add]
  | succ n =>
    refine gradedPsi_injective hE n ?_
    calc gradedPsi hE n (gradedSymbol hE (n + 1) (a + b))
        = formalNeighborhoodProjection D (n + 1) (a + b) :=
          gradedPsi_gradedSymbol hE n (add_mem ha hb)
      _ = formalNeighborhoodProjection D (n + 1) a +
            formalNeighborhoodProjection D (n + 1) b := map_add _ _ _
      _ = gradedPsi hE n (gradedSymbol hE (n + 1) a) +
            gradedPsi hE n (gradedSymbol hE (n + 1) b) := by
          rw [gradedPsi_gradedSymbol hE n ha, gradedPsi_gradedSymbol hE n hb]
      _ = gradedPsi hE n (gradedSymbol hE (n + 1) a + gradedSymbol hE (n + 1) b) :=
          ((gradedPsi hE n).map_add _ _).symm

/-- The symbol is semilinear over the residue homomorphism on each step of the filtration. -/
public theorem gradedSymbol_smul (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ)
    (c : formalNeighborhoodRing D) {a : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D n) :
    gradedSymbol hE n (c * a) = formalNeighborhoodScalar D k e c • gradedSymbol hE n a := by
  cases n with
  | zero =>
    rw [gradedSymbol_zero_apply, gradedSymbol_zero_apply, map_mul, ← smul_eq_mul]
    exact (residueEquivZero hE).map_smul _ _
  | succ n =>
    refine gradedPsi_injective hE n ?_
    rw [gradedPsi_smul_scalar, gradedPsi_gradedSymbol hE n (Ideal.mul_mem_left _ _ ha),
      gradedPsi_gradedSymbol hE n ha, map_mul]

/-- The symbol of an element of `Iₙ` vanishes exactly when it lies in `Iₙ₊₁`. -/
public theorem gradedSymbol_eq_zero_iff (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ)
    {a : formalNeighborhoodRing D} (ha : a ∈ formalNeighborhoodFiltration D n) :
    gradedSymbol hE n a = 0 ↔ a ∈ formalNeighborhoodFiltration D (n + 1) := by
  cases n with
  | zero =>
    rw [gradedSymbol_zero_apply, (residueEquivZero hE).map_eq_zero_iff, ← RingHom.mem_ker,
      ker_formalNeighborhoodScalar]
  | succ n =>
    exact (mem_succ_iff_gradedPsi hE n _ (gradedPsi_gradedSymbol hE n ha).symm).symm

/-- Every element of `Γ(X, 𝒪_X(-D ^ n)|_D)` is the symbol of an element of `Iₙ`. -/
public theorem gradedSymbol_surjective (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ)
    (v : restrictedNegativeTwistSections D k e n) :
    ∃ a ∈ formalNeighborhoodFiltration D n, gradedSymbol hE n a = v := by
  cases n with
  | zero =>
    obtain ⟨a, ha⟩ := hE.surjective_formalNeighborhoodScalar ((residueEquivZero hE).symm v)
    exact ⟨a, Submodule.mem_top,
      by rw [gradedSymbol_zero_apply, ha, LinearEquiv.apply_symm_apply]⟩
  | succ n =>
    obtain ⟨a, ha, hav⟩ := exists_mem_gradedPsi hE n v
    exact ⟨a, ha, gradedPsi_injective hE n ((gradedPsi_gradedSymbol hE n ha).trans hav)⟩

/-! ### The degreewise symbol system -/

/-- **The degreewise symbol system on the projection-kernel filtration of an exceptional curve of
the first kind.** The graded pieces `Iₙ / Iₙ₊₁` are presented, one degree at a time, by the
spaces `Γ(X, 𝒪_X(-D ^ n)|_D)` of dimension `n + 1`; no compatibility between the degrees is
asserted, and none is available.

Together with degree-one generation of the associated graded ring this produces all five
geometric inputs of [Stacks, Tag 0C2K], by
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofDegreewiseSymbol`. -/
public def degreewiseSymbol (hE : IsExceptionalCurveOfFirstKind D k e) :
    SemistableReduction.DegreewiseSymbol (formalNeighborhoodRing D) k :=
  SemistableReduction.DegreewiseSymbol.ofGradedPresentation
    (formalNeighborhoodFiltration D) (formalNeighborhoodScalar D k e)
    (fun n => restrictedNegativeTwistSections D k e n) (gradedSymbol hE)
    hE.finrank_restrictedNegativeTwistSections (formalNeighborhoodFiltration_zero D)
    (formalNeighborhoodFiltration_succ_le D) (formalNeighborhoodFiltration_mul_le D)
    (ker_formalNeighborhoodScalar D k e) hE.surjective_formalNeighborhoodScalar
    (fun n _ _ ha hb => gradedSymbol_add hE n ha hb)
    (fun n c _ ha => gradedSymbol_smul hE n c ha)
    (fun n _ ha => gradedSymbol_eq_zero_iff hE n ha) (gradedSymbol_surjective hE)

@[simp]
public theorem degreewiseSymbol_ideal (hE : IsExceptionalCurveOfFirstKind D k e) :
    (degreewiseSymbol hE).ideal = formalNeighborhoodFiltration D := rfl

end IsExceptionalCurveOfFirstKind

namespace ExceptionalMonomialData

/-- **The five geometric inputs of [Stacks, Tag 0C2K] from degree-one generation alone.** For an
exceptional curve of the first kind, every input of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData` follows from the single
statement that the associated graded ring of the projection-kernel filtration is generated in
degree one:

`Iₙ₊₁ ⊆ I₁ Iₙ + Iₙ₊₂`.

Multiplicativity of the filtration and the residue quotient being a field were already proved
unconditionally; the degreewise symbol system
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.degreewiseSymbol` and
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofDegreewiseSymbol` supply the
three monomial statements from `hgen`.

`hgen` is not a consequence of the symbol system: a degreewise presentation constrains each
graded piece separately, so it determines the associated graded ring only up to its Hilbert
function, and a graded `k`-algebra with `dim Gₙ = n + 1` need not be generated in degree one.
What it needs is the multiplicativity of the identification of the graded pieces with the
sections of a twist: the multiplication on those sections is
`Stacks.Divisors.restrictedIdealMulSections`, the symbols are multiplicative for it, and the
identification with `H⁰(𝐏¹_k, 𝒪(m))` is made multiplicative in
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistMultiplicative.lean`. `hgen` is
therefore discharged for an exceptional curve of the first kind, by
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`
`.ofIsExceptionalCurveOfFirstKind`. -/
public def ofExceptionalCurve (hE : IsExceptionalCurveOfFirstKind D k e)
    (hgen : ∀ n, formalNeighborhoodFiltration D (n + 1) ≤
      formalNeighborhoodFiltration D 1 * formalNeighborhoodFiltration D n ⊔
        formalNeighborhoodFiltration D (n + 2)) :
    ExceptionalMonomialData D :=
  ofDegreewiseSymbol k hE hE.degreewiseSymbol rfl hgen

end ExceptionalMonomialData

end AlgebraicGeometry.Scheme.IdealSheafData

end
