module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalRelativeMorphismsImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorNumericalSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariantsTwistPerfect

/-!
# `Mor^P_Q(Z, X)` for the numerical invariants of Situation 0DNC (Stacks 0DPQ)

Let `z : Z ⟶ Q` be flat, proper and of finite presentation and `x : X ⟶ Q` separated and of
finite presentation, morphisms of algebraic spaces over a scheme `S` of a big fppf site.  Let `I`
be a set, `E_i ∈ D(𝒪_{Z ×_Q X})` perfect for `i ∈ I` and `P : I → ℤ`, the standing data
`AlgebraicGeometry.Space.NumericalSituation` of Stacks 0DNC on the coherent situation of
`Z ×_Q X ⟶ Q`.  Since `Mor_Q(Z, X) ⊆ Hilb_{Z ×_Q X / Q}` is an open subspace through the graph
transformation (Stacks 0D1A, 0D1B), Stacks 0DPQ defines

`Mor^P_Q(Z, X) = Mor_Q(Z, X) ∩ Hilb^P_{Z ×_Q X / Q}`,

with `Hilb^P` the subfunctor of Stacks 0DPG: the families `W ⊆ (Z ×_Q X)_T` whose object
`(T, 𝒪_W)` of `Coh_{Z ×_Q X / Q}` has `χ_i(t) = χ(K_i ⊗^𝐋 κ(t)) = P(i)` for all `i` and `t`,
where `K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝒪_W)`.  So a relative morphism `(a, b)` over `T` lies in
`Mor^P_Q(Z, X)` exactly when its graph has these invariants.  The remark asserts that
`Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed immersion, and an open and closed immersion when
`I` is finite, or `Q` is locally Noetherian, or `I = ℤ` and `E_i = 𝓛^{⊗ i}` for an invertible
`𝒪_{Z ×_Q X}`-module `𝓛`, in which case the notation is `Mor^{P, 𝓛}_Q(Z, X)`.

The source deduces every one of these assertions by base change along the graph transformation
from the corresponding assertion about `Coh^P_{Z ×_Q X / Q} ⊆ Coh_{Z ×_Q X / Q}` (Stacks 0DND,
0DNE), through `Hilb^P` (Stacks 0DPG) and `Quot^P` (Stacks 0DP6).  This file carries out that base
change for the invariants of Situation 0DNC themselves.

## Main definitions

All names in the two lists below are in the namespace `AlgebraicGeometry.Space`.

* `prescribedRelativeHom`: `Mor^P_Q(Z, X)`, the subfunctor of `Mor_Q(Z, X)` of the relative
  morphisms whose graph lies in `Hilb^P_{Z ×_Q X / Q}`.
* `hilbertPolynomialRelativeHom`: `Mor^{P, 𝓛}_Q(Z, X)`, the case `I = ℤ`, `E_n = 𝓛^{⊗ n}`.

## Main results

* `mem_prescribedRelativeHom_iff`: a relative morphism lies in `Mor^P_Q(Z, X)` exactly when the
  object of `Coh_{Z ×_Q X / Q}` of its graph lies in `Coh^P_{Z ×_Q X / Q}`.
* `isFlat_and_isClosedImmersion_prescribedRelativeHom_ι_of_isFlatClosedCondition` and
  `isOpenImmersion_and_isClosedImmersion_prescribedRelativeHom_ι_of_isOpenAndClosedCondition`:
  if `Coh^P_{Z ×_Q X / Q} ⊆ Coh_{Z ×_Q X / Q}` is a flat closed, respectively open and closed,
  substack, then `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed, respectively open and closed,
  immersion, by base change.
* `isFlat_and_isClosedImmersion_prescribedRelativeHom_ι` and
  `isOpenImmersion_and_isClosedImmersion_prescribedRelativeHom_ι`: when the functions `χ_i` are
  locally constant, `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed immersion, and an open and
  closed immersion for finite `I`.

## Implementation notes

The definition of `Mor^P_Q(Z, X)` as a subfunctor needs the invariants `χ_i` to be compatible
with pullback along the morphisms of `Coh_{Z ×_Q X / Q}`, which is the base change part of
Stacks 0A1P in Situation 0DNC; it enters, as in
`AlgebraicGeometry.Space.numericalHilbertCondition`, as the hypothesis `hbc`.  Local constancy of
the `χ_i`, which the source deduces from the perfectness of `K_i` (Stacks 0A1P) and Stacks 0D1Z,
is the hypothesis `hlc` of the last two results.

## References

* [Stacks Project, Tag 0DPQ](https://stacks.math.columbia.edu/tag/0DPQ)
* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0D1A](https://stacks.math.columbia.edu/tag/0D1A)
* [Stacks Project, Tag 0D1B](https://stacks.math.columbia.edu/tag/0D1B)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe v u

attribute [local instance] pointTopology

section Prescribed

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    {hZ : IsAlgebraicSpace B S hS Z} {hX : IsAlgebraicSpace B S hS X}
    {hQ : IsAlgebraicSpace B S hS Q}
    (hsep : IsSeparated B S hS x) (hx_fp : IsFinitePresentation B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)
    (N : NumericalSituation.{u, v, u} B S hS
      (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)).toCoherentSituation)
    (hbc : ∀ {A' A : CoherentObject (structureSheafQuotSituation
        (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)).toCoherentSituation}
      (φ : CoherentHom A' A) (i : N.I) (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))

/-- **`Mor^P_Q(Z, X) = Mor_Q(Z, X) ∩ Hilb^P_{Z ×_Q X / Q}`** (Stacks 0DPQ): the subfunctor of
the relative morphism functor of the relative morphisms whose graph, a point of
`Hilb_{Z ×_Q X / Q}` by Stacks 0D1A, lies in `Hilb^P_{Z ×_Q X / Q}` of Stacks 0DPG, that is,
whose graph `W` has `χ(K_i ⊗^𝐋 κ(t)) = P(i)` for `K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝒪_W)`, every
`i ∈ I` and every point `t` of the test scheme. -/
def prescribedRelativeHom : Subfunctor (relativeHom B S hS Z X Q z x hZ hX hQ) :=
  relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper
    (numericalHilbertCondition (graphAmbientMap B S hS z x hZ hX hQ)
      (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp) hbc)

/-- A relative morphism lies in `Mor^P_Q(Z, X)` exactly when its graph lies in
`Hilb^P_{Z ×_Q X / Q}`. -/
theorem mem_prescribedRelativeHom_iff_mem_numericalHilbertCondition {T : (BigFppfOver B S hS)ᵒᵖ}
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj T) :
    s ∈ (prescribedRelativeHom hsep hx_fp hfp hflat hproper N hbc).obj T ↔
      (graphTransformation hZ hX hQ hsep hfp hflat hproper).app T (ULift.up s) ∈
        (numericalHilbertCondition (graphAmbientMap B S hS z x hZ hX hQ)
          (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp) hbc).obj T :=
  Iff.rfl

/-- A relative morphism lies in `Mor^P_Q(Z, X)` exactly when the object `(T, 𝒪_W)` of
`Coh_{Z ×_Q X / Q}` of its graph `W` lies in `Coh^P_{Z ×_Q X / Q}`. -/
theorem mem_prescribedRelativeHom_iff {T : (BigFppfOver B S hS)ᵒᵖ}
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj T) :
    s ∈ (prescribedRelativeHom hsep hx_fp hfp hflat hproper N hbc).obj T ↔
      N.HasNumericalInvariants (hilbertCohObject (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)
        ((graphTransformation hZ hX hQ hsep hfp hflat hproper).app T (ULift.up s))) :=
  Iff.rfl

/-- **`Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed immersion as soon as `Coh^P_{Z ×_Q X / Q}`
is a flat closed substack of `Coh_{Z ×_Q X / Q}`**: it is the base change of
`Coh^P ⟶ Coh` along `Mor_Q(Z, X) ⟶ Hilb_{Z ×_Q X / Q} = Quot_{𝒪/Z ×_Q X/Q} ⟶ Coh`. -/
theorem isFlat_and_isClosedImmersion_prescribedRelativeHom_ι_of_isFlatClosedCondition
    (hQc : CoherentSituation.IsFlatClosedCondition _ N.HasNumericalInvariants) :
    IsFlat B S hS (prescribedRelativeHom hsep hx_fp hfp hflat hproper N hbc).ι ∧
      IsClosedImmersion B S hS (prescribedRelativeHom hsep hx_fp hfp hflat hproper N hbc).ι :=
  isFlat_and_isClosedImmersion_graphPreimage_hilbertCondition_ι B S hS Z X Q z x hZ hX hQ hsep
    hfp hflat hproper hx_fp (CoherentSituation.numerical_points_of_hom N.P hbc)
    (CoherentSituation.isFlatClosedCondition_iff_isCutOutOnTestSchemes.1 hQc)

/-- **`Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is an open and closed immersion as soon as
`Coh^P_{Z ×_Q X / Q}` is an open and closed substack of `Coh_{Z ×_Q X / Q}`**, by base change. -/
theorem isOpenImmersion_and_isClosedImmersion_prescribedRelativeHom_ι_of_isOpenAndClosedCondition
    (hQc : CoherentSituation.IsOpenAndClosedCondition _ N.HasNumericalInvariants) :
    IsOpenImmersion B S hS (prescribedRelativeHom hsep hx_fp hfp hflat hproper N hbc).ι ∧
      IsClosedImmersion B S hS (prescribedRelativeHom hsep hx_fp hfp hflat hproper N hbc).ι :=
  isOpenImmersion_and_isClosedImmersion_graphPreimage_hilbertCondition_ι B S hS Z X Q z x hZ hX
    hQ hsep hfp hflat hproper hx_fp (CoherentSituation.numerical_points_of_hom N.P hbc)
    hQc.isCutOutOnTestSchemes

/-- **`Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed immersion** when the functions `χ_i` of
Situation 0DNC are locally constant: `Coh^P_{Z ×_Q X / Q}` is then the intersection of the open
and closed substacks `Coh^{P|_J}` over the finite subsets `J ⊆ I`, a flat closed substack. -/
theorem isFlat_and_isClosedImmersion_prescribedRelativeHom_ι
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i)) :
    IsFlat B S hS (prescribedRelativeHom hsep hx_fp hfp hflat hproper N hbc).ι ∧
      IsClosedImmersion B S hS (prescribedRelativeHom hsep hx_fp hfp hflat hproper N hbc).ι :=
  isFlat_and_isClosedImmersion_prescribedRelativeHom_ι_of_isFlatClosedCondition hsep hx_fp hfp
    hflat hproper N hbc (N.isFlatClosedCondition_hasNumericalInvariants hbc hlc)

/-- **For a finite index set `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is an open and closed immersion**
when the functions `χ_i` of Situation 0DNC are locally constant: a finite intersection of open
and closed loci is open and closed. -/
theorem isOpenImmersion_and_isClosedImmersion_prescribedRelativeHom_ι [Finite N.I]
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i)) :
    IsOpenImmersion B S hS (prescribedRelativeHom hsep hx_fp hfp hflat hproper N hbc).ι ∧
      IsClosedImmersion B S hS (prescribedRelativeHom hsep hx_fp hfp hflat hproper N hbc).ι :=
  isOpenImmersion_and_isClosedImmersion_prescribedRelativeHom_ι_of_isOpenAndClosedCondition hsep
    hx_fp hfp hflat hproper N hbc (N.isOpenAndClosedCondition_hasNumericalInvariants hbc hlc)

end Prescribed

section HilbertPolynomial

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    {hZ : IsAlgebraicSpace B S hS Z} {hX : IsAlgebraicSpace B S hS X}
    {hQ : IsAlgebraicSpace B S hS Q}
    (hsep : IsSeparated B S hS x) (hx_fp : IsFinitePresentation B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)

/-- The standing data of Situation 0DNC on `Z ×_Q X ⟶ Q` for the index set `ℤ` and the twists
`n ↦ 𝓛^{⊗ n}` of an invertible module `𝓛` on `Z ×_Q X`, with prescribed invariants `P`. -/
abbrev graphAmbientHilbertPolynomialSituation
    (L : Modules.{u, u} B S hS (graphAmbient B S hS z x hZ hX hQ).1
      (graphAmbient B S hS z x hZ hX hQ).2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS
        (graphAmbient B S hS z x hZ hX hQ).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (graphAmbient B S hS z x hZ hX hQ).1 (graphAmbient B S hS z x hZ hX hQ).2).O)).property L]
    (P : ℤ → ℤ) :
    NumericalSituation.{u, 0, u} B S hS
      (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)).toCoherentSituation :=
  NumericalSituation.ofHilbertPolynomial B S hS _
    (isSeparated_graphAmbientMap z x hZ hX hQ hproper.1 hsep) L (hL := hL) P

/-- **`Mor^{P, 𝓛}_Q(Z, X)`** (Stacks 0DPQ): `Mor^P_Q(Z, X)` for `I = ℤ` and `E_n = 𝓛^{⊗ n}`, an
invertible `𝒪_{Z ×_Q X}`-module `𝓛`, the relative morphisms whose graph `W` has
`χ((Z ×_Q X)_t, 𝓛_t^{⊗ n} ⊗ 𝒪_{W_t}) = P(n)` for all `n` and all points `t`. -/
abbrev hilbertPolynomialRelativeHom
    (L : Modules.{u, u} B S hS (graphAmbient B S hS z x hZ hX hQ).1
      (graphAmbient B S hS z x hZ hX hQ).2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS
        (graphAmbient B S hS z x hZ hX hQ).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (graphAmbient B S hS z x hZ hX hQ).1 (graphAmbient B S hS z x hZ hX hQ).2).O)).property L]
    (P : ℤ → ℤ)
    (hbc : ∀ {A' A : CoherentObject (structureSheafQuotSituation
        (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)).toCoherentSituation}
      (φ : CoherentHom A' A) (i : ℤ) (t : points B S hS (yoneda.obj A'.T.left)),
      (graphAmbientHilbertPolynomialSituation hsep hx_fp hfp hproper L P).numericalEuler A' i t =
        (graphAmbientHilbertPolynomialSituation hsep hx_fp hfp hproper L P).numericalEuler A i
          (pointsMap B S hS _ (yoneda.map φ.base.left) t)) :
    Subfunctor (relativeHom B S hS Z X Q z x hZ hX hQ) :=
  prescribedRelativeHom hsep hx_fp hfp hflat hproper
    (graphAmbientHilbertPolynomialSituation hsep hx_fp hfp hproper L P) hbc

end HilbertPolynomial

end AlgebraicGeometry.Space

end
