module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ProperOverLocalBaseCharts
public import StacksFrontier.AlgebraicGeometry.Duality.SurfaceDualizingDegree.NormalSurface
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve

/-!
# `ω_X^• = f^!ω_S^•` on a normal surface is its dualizing module in degree `-2`

Let `S` be affine with `A = Γ(S, ⊤)` a Noetherian local ring, let `ω_S^•` be modelled on `S` by a
*normalized* dualizing complex `ω_A^•` over `A`, and let `f : X ⟶ S` be proper. Write
`ω_X^• = f^!ω_S^• = a(ω_S^•)` for the twisted inverse image of [Stacks, Tag 0A9E] applied to
`ω_S^•`. This file records the three properties of `ω_X^•` which together determine the degree in
which it is concentrated:

1. it *is* `a(ω_S^•)`, by definition of `Stacks.Duality.relativeDualizingComplex`;
2. it is a dualizing complex on `X` ([Stacks, Tag 0AA3]);
3. it is normalized at the closed points of `X`: the associated shift function of
   [Stacks, Tag 0AWF] vanishes there.

The third is the one that cannot be read off `X` alone. A shift of a dualizing complex is again a
dualizing complex, so no condition on `X` and on `ω_X^•` being dualizing can pin the degree of
concentration; what pins it is the normalization of `ω_A^•` on the base, transported to `X` along
`f^!`. The transport is the chart description of `f^!` ([Stacks, Tag 0BV2]): over an affine
`U ⊆ X` the complex `ω_X^•|_U` is the associated sheaf of the algebraic upper shriek of `ω_A^•`
along a polynomial presentation of `A → Γ(X, U)`, a closed point of `X` lies over the closed point
of `S` because `f` is closed, and there [Stacks, Tag 0E9N] computes the shift function to be zero.

Consequently, when `X` is a connected Noetherian normal scheme of dimension two,
`Stacks.Duality.dualizingComplexIsoShiftTwoOfIsNormalSurface` applies to `ω_X^•` and gives

`ω_X^• ≅ ω_X[2]`, `ω_X = H^{-2}(ω_X^•)`,

with `ω_X` a coherent Cohen–Macaulay `𝒪_X`-module. The last section specialises this to the
situation of [Stacks, Tag 0AX8]: a two-dimensional Noetherian normal local domain `(A, 𝔪, κ)`, a
modification `f : X ⟶ Spec(A)` and `X` normal.

## Main results

All in the namespace `Stacks.Duality`.

* `relativeDualizingComplex_eq_twistedInverseImage_obj` — `ω_X^•` is `a(ω_S^•)`.
* `hasTopCharts_relativeDualizingComplex` — the chart description of `ω_X^•` over the affine
  open `⊤` of `S`.
* `isDualizingComplex_relativeDualizingComplex` — `ω_X^•` is a dualizing complex.
* `associatedShiftFunction_relativeDualizingComplex_eq_zero` — `ω_X^•` is normalized at the
  closed points of `X`.
* `relativeDualizingModule_eq_homology_neg_two` — on a surface `ω_X` is `H^{-2}(ω_X^•)`.
* `relativeDualizingComplexIsoShiftTwoOfIsNormalSurface` — **`ω_X^• ≅ ω_X[2]`**.
* `coherent_cohenMacaulay_relativeDualizingModule_of_isNormalSurface` — `ω_X` is coherent and
  Cohen–Macaulay.
* `AlgebraicGeometry.VanishingSituation.relativeDualizingComplexIsoShiftTwo` and
  `.coherent_cohenMacaulay_relativeDualizingModule` — the same two statements in the situation of
  [Stacks, Tag 0AX8] with `X` normal.

## Implementation notes

Every derived category of `𝒪`-modules below is read at
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the locally small model, because that is
where the right adjoint of [Stacks, Tag 0A9E] — and hence `ω_X^•` itself — exists. The model of
`D(A)` carrying `ω_A^•` is the one fixed by `Stacks.Duality.IsTildeModelOnAnyModel` and
`Dualizing.IsNormalizedDualizingComplex`. No instance is installed in this file, so the statements
read at whichever model their constituents are already phrased at; the inputs from
`StacksFrontier/AlgebraicGeometry/Duality/SurfaceDualizingDegree/NormalSurface.lean` carry a free
`HasDerivedCategory` binder and therefore specialise to it.

The base's normalized complex enters as a model `ω_A^•` over `Γ(S, ⊤)` together with the
hypothesis that `ω_S^•` is its associated sheaf on `⊤`, which is the shape in which
[Stacks, Tag 0AWI] and [Stacks, Tag 0AWN] are already stated here
(`Stacks.Duality.isDualizingModuleOf_relativeDualizingModule`,
`Stacks.Duality.vanishing_and_support_relativeDualizingComplex`).

## References

* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0AWN](https://stacks.math.columbia.edu/tag/0AWN)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0E9N](https://stacks.math.columbia.edu/tag/0E9N)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0B3D](https://stacks.math.columbia.edu/tag/0B3D)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

open ChartCompactification _root_.Stacks.Duality.ProjectiveSpace
  _root_.AlgebraicGeometry.ProjectiveSpace Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X S : Scheme.{u}} [IsAffine S] [AlgebraicGeometry.IsNoetherian S]
  [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]

/-! ### `ω_X^•` is `a(ω_S^•)`, dualizing, and normalized at the closed points -/

omit [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)] in
/-- **`ω_X^• = f^!ω_S^•` is `a(ω_S^•)`**, the value at `ω_S^•` of the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` of [Stacks, Tag 0A9E]. This holds by the definition of
`Stacks.Duality.relativeDualizingComplex`, and is recorded so that statements phrased against the
right adjoint apply to it verbatim. -/
theorem relativeDualizingComplex_eq_twistedInverseImage_obj (f : X ⟶ S) [IsProper f]
    (ωS : quasiCoherentDerivedCategory S) :
    relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS =
      (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj ωS :=
  rfl

omit [IsLocalRing Γ(S, ⊤)] in
/-- **The chart description of `ω_X^• = f^!ω_S^•` over the affine open `⊤` of `S`**: for every
affine `U ⊆ X` and every polynomial presentation of `Γ(S, ⊤) → Γ(X, U)`, the restriction
`ω_X^•|_U` is the associated sheaf of the algebraic upper shriek of the model `ω_A^•`. This is
[Stacks, Tag 0BV2] at the identity compactification of `f`, transported along
`Stacks.Duality.upperShriekProperIso`, which identifies `f^!` there with the right adjoint `a`. -/
theorem hasTopCharts_relativeDualizingComplex (f : X ⟶ S) [IsProper f]
    (ωS : quasiCoherentDerivedCategory S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : @Dualizing.IsDualizingComplex Γ(S, ⊤) _ _
      (HasDerivedCategory.standard (ModuleCat.{u} Γ(S, ⊤))) ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    HasTopCharts f ω (relativeDualizingComplex f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS).obj := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsProper (ftsHomToBase f).left := ‹IsProper f›
  have hdual : IsDualizingComplex ωS.obj := isDualizingComplex_of_isTildeModelOn_top hω hmodel
  have hcharts := UpperShriekCharts.hasTopCharts f
    (upperShriekCharts (ftsHomToBase f) (properCompactification (ftsHomToBase f)) ωS
      (isBoundedBelow_of_isDualizingComplex _ hdual)) hmodel
  exact fun U hU p => isTildeModelOnAnyModel_of_iso ((ObjectProperty.ι _).mapIso
    ((upperShriekProperIso (ftsHomToBase f)).app ωS)) (hcharts U hU p)

omit [IsLocalRing Γ(S, ⊤)] in
/-- **`ω_X^• = f^!ω_S^•` is a dualizing complex on `X`** ([Stacks, Tag 0AA3]): on each affine
chart it is the algebraic upper shriek of a dualizing complex, which is dualizing, and dualizing
complexes glue. -/
theorem isDualizingComplex_relativeDualizingComplex (f : X ⟶ S) [IsProper f]
    (ωS : quasiCoherentDerivedCategory S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : @Dualizing.IsDualizingComplex Γ(S, ⊤) _ _
      (HasDerivedCategory.standard (ModuleCat.{u} Γ(S, ⊤))) ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsDualizingComplex (relativeDualizingComplex f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS).obj :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  isDualizingComplex_of_hasTopCharts f hω
    (hasTopCharts_relativeDualizingComplex f ωS ω hω hmodel)

/-- **`ω_X^• = f^!ω_S^•` is normalized at the closed points of `X`** when `ω_A^•` is a normalized
dualizing complex over `A = Γ(S, ⊤)`: the associated shift function of [Stacks, Tag 0AWF] vanishes
at every closed point.

This is the transport of the normalization from the base to `X` along `f^!`. A closed point
`x ∈ X` maps to the closed point of `S`, because `f` is proper and hence closed; on an affine
`U ∋ x` the complex `ω_X^•|_U` is the algebraic upper shriek of `ω_A^•` along a polynomial
presentation of `A → Γ(X, U)`, and the upper shriek of a normalized dualizing complex is
normalized at a maximal ideal lying over the maximal ideal of `A` ([Stacks, Tag 0E9N]). -/
theorem associatedShiftFunction_relativeDualizingComplex_eq_zero (f : X ⟶ S) [IsProper f]
    (ωS : quasiCoherentDerivedCategory S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    associatedShiftFunction (relativeDualizingComplex f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS).obj x = 0 :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  associatedShiftFunction_eq_zero_of_hasTopCharts f hω
    (hasTopCharts_relativeDualizingComplex f ωS ω hω.1 hmodel) x hx

/-! ### `ω_X^• ≅ ω_X[2]` -/

omit [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)] in
/-- On a scheme of dimension two the relative dualizing module `ω_X = H^{-dim X}(ω_X^•)` of
[Stacks, Tag 0AWI] is `H^{-2}(ω_X^•)`. -/
theorem relativeDualizingModule_eq_homology_neg_two (f : X ⟶ S) [IsProper f]
    (hX : topologicalKrullDim X = 2) (ωS : quasiCoherentDerivedCategory S) :
    relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS =
      (DerivedCategory.homologyFunctor X.Modules (-2 : ℤ)).obj
        (relativeDualizingComplex f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS).obj := by
  have hdeg : (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ)) = (-2 : ℤ) := by
    rw [hX]; rfl
  change (DerivedCategory.homologyFunctor X.Modules
    (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ))).obj _ = _
  rw [hdeg]

/-- **`ω_X^• ≅ ω_X[2]` for a normal surface over a local base.** Let `S` be affine with
`A = Γ(S, ⊤)` a Noetherian local ring, let `ω_S^•` be modelled on `S` by a normalized dualizing
complex `ω_A^•` over `A`, let `f : X ⟶ S` be proper with `X` a connected Noetherian normal scheme
of dimension two, and let `ω_X^• = f^!ω_S^• = a(ω_S^•)`. Then `ω_X^•` is the dualizing module
`ω_X = H^{-2}(ω_X^•)` placed in degree `-2`.

The two inputs of
`Stacks.Duality.dualizingComplexIsoShiftTwoOfIsNormalSurface` are supplied by
`Stacks.Duality.isDualizingComplex_relativeDualizingComplex` and
`Stacks.Duality.associatedShiftFunction_relativeDualizingComplex_eq_zero`; the second is where the
normalization of `ω_A^•` is used, and without it the degree of concentration is not determined. -/
def relativeDualizingComplexIsoShiftTwoOfIsNormalSurface (f : X ⟶ S) [IsProper f]
    [ConnectedSpace X] (hnormal : IsNormal X) (hX : topologicalKrullDim X = 2)
    (ωS : quasiCoherentDerivedCategory S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω) :
    letI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
    (relativeDualizingComplex f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS).obj ≅
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (relativeDualizingModule f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS))⟦(2 : ℤ)⟧ :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  dualizingComplexIsoShiftTwoOfIsNormalSurface hnormal hX _
      (isDualizingComplex_relativeDualizingComplex f ωS ω hω.1 hmodel)
      (fun x hx =>
        associatedShiftFunction_relativeDualizingComplex_eq_zero f ωS ω hω hmodel x hx) ≪≫
    eqToIso (by rw [relativeDualizingModule_eq_homology_neg_two f hX ωS])

/-- **`ω_X = H^{-2}(ω_X^•)` is a coherent Cohen–Macaulay module on a normal surface over a local
base**, the dualizing module of [Stacks, Tag 0AWI] for `ω_X^• = f^!ω_S^•` with `ω_A^•`
normalized. -/
theorem coherent_cohenMacaulay_relativeDualizingModule_of_isNormalSurface (f : X ⟶ S) [IsProper f]
    [ConnectedSpace X] (hnormal : IsNormal X) (hX : topologicalKrullDim X = 2)
    (ωS : quasiCoherentDerivedCategory S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω) :
    _root_.SheafOfModules.IsCoherent (relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS) ∧
      AlgebraicGeometry.SheafIsCohenMacaulay X (relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have h := coherent_cohenMacaulay_homology_neg_two_of_isNormalSurface hnormal hX _
    (isDualizingComplex_relativeDualizingComplex f ωS ω hω.1 hmodel)
    (associatedShiftFunction_relativeDualizingComplex_eq_zero f ωS ω hω hmodel)
  rwa [relativeDualizingModule_eq_homology_neg_two f hX ωS]

end Stacks.Duality

/-! ### The vanishing situation -/

namespace AlgebraicGeometry.VanishingSituation

open Stacks.Duality

variable (V : VanishingSituation.{u})

/-- The ring of global sections of the affine base is the local ring of the situation. -/
def baseGlobalSectionsRingEquiv : V.A ≃+* Γ(V.base, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of V.A)).symm.commRingCatIsoToRingEquiv

/-- The global sections of the affine base form a Noetherian ring. -/
theorem isNoetherianRing_globalSections_base : IsNoetherianRing Γ(V.base, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V.base⟩

/-- The global sections of the affine base form a local ring. -/
theorem isLocalRing_globalSections_base : IsLocalRing Γ(V.base, ⊤) :=
  V.baseGlobalSectionsRingEquiv.isLocalRing

attribute [local instance] isNoetherianRing_globalSections_base isLocalRing_globalSections_base

/-- **A modification of the spectrum of the local ring of the situation is two-dimensional.** A
proper birational morphism of integral schemes preserves dimension, and `dim Spec(A) = 2`. -/
theorem topologicalKrullDim_source : topologicalKrullDim V.X = 2 := by
  have hmod := V.modification
  have : IsProper V.f := hmod.isProper
  have : IsIntegral V.X := hmod.source_isIntegral
  have h : topologicalKrullDim V.X = ringKrullDim V.A := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hmod.isBirational.topologicalKrullDim_eq_of_isClosedMap V.f.isClosedMap
  rw [h, V.dimension_two]

/-- **`ω_X^• ≅ ω_X[2]` in the situation of [Stacks, Tag 0AX8] with `X` normal.** Let `(A, 𝔪, κ)`
be a two-dimensional Noetherian normal local domain, `f : X ⟶ Spec(A)` a modification with `X`
normal, and `ω_S^•` the complex on `Spec(A)` associated with a normalized dualizing complex
`ω_A^•` over `A`. Then `ω_X^• = f^!ω_S^• = a(ω_S^•)` is a dualizing complex on `X`, normalized at
the closed points, and equals its dualizing module `ω_X = H^{-2}(ω_X^•)` shifted by two.

`X` is irreducible, hence connected, because a modification has integral source; it is
two-dimensional because a proper birational morphism of integral schemes preserves dimension; and
it is Noetherian because `f` is of finite type over the Noetherian `Spec(A)`. -/
def relativeDualizingComplexIsoShiftTwo [IsNormal V.X]
    (ωS : quasiCoherentDerivedCategory V.base)
    (ω : DerivedCategory (ModuleCat.{u} Γ(V.base, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top V.base) ω) :
    letI : AlgebraicGeometry.IsNoetherian V.X := isNoetherian_of_locallyOfFiniteType V.f
    (relativeDualizingComplex V.f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs V.f) ωS).obj ≅
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj
        (relativeDualizingModule V.f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs V.f) ωS))⟦(2 : ℤ)⟧ :=
  relativeDualizingComplexIsoShiftTwoOfIsNormalSurface V.f ‹IsNormal V.X›
    V.topologicalKrullDim_source ωS ω hω hmodel

/-- **`ω_X` is a coherent Cohen–Macaulay module** in the situation of [Stacks, Tag 0AX8] with `X`
normal: a Noetherian normal scheme of dimension at most two is Cohen–Macaulay
([Stacks, Tag 0B3D]), and `ω_X = H^{-2}(ω_X^•)` is the dualizing module of [Stacks, Tag 0AWI]. -/
theorem coherent_cohenMacaulay_relativeDualizingModule [IsNormal V.X]
    (ωS : quasiCoherentDerivedCategory V.base)
    (ω : DerivedCategory (ModuleCat.{u} Γ(V.base, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top V.base) ω) :
    _root_.SheafOfModules.IsCoherent (relativeDualizingModule V.f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs V.f) ωS) ∧
      AlgebraicGeometry.SheafIsCohenMacaulay V.X (relativeDualizingModule V.f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs V.f) ωS) :=
  coherent_cohenMacaulay_relativeDualizingModule_of_isNormalSurface V.f ‹IsNormal V.X›
    V.topologicalKrullDim_source ωS ω hω hmodel

end AlgebraicGeometry.VanishingSituation

end
