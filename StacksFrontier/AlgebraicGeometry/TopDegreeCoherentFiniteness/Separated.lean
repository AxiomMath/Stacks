module

public import StacksFrontier.AlgebraicGeometry.CohomologyOverField.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite dimensionality of the top-degree cohomology on a separated scheme of finite type

[Stacks, Tag 0A3M]: let `X` be a separated scheme of finite type over a field `k`, let `ℱ` be a
coherent `𝒪_X`-module and let `d = dim(X)`. Then `H^d(X, ℱ)` is a finite-dimensional
`k`-vector space.

## The argument

The source proves this by induction on `d`, reducing to the structure sheaf of a variety and
then using Chow's lemma, relative ampleness and the Leray spectral sequence to land on an open of
a projective variety, where it concludes with [Stacks, Tag 0A3G] clause (2) and
[Stacks, Tag 01YS]. Here the same final step is reached in one move, by Nagata's compactification
theorem ([Stacks, Tag 0F41],
`AlgebraicGeometry.hasCompactification_of_compactSpace_quasiSeparatedSpace`, proved in this
repository):

1. `X ⟶ Spec k` is separated and of finite type over the Noetherian `Spec k`, so it factors as a
   quasi-compact open immersion `j : X ⟶ P` followed by a proper `P ⟶ Spec k`.
2. Replace `P` by the scheme-theoretic image `X̄` of `j`. It is proper over `k`, `X` is a dense
   open of it, and so `dim X̄ ≤ dim X = d`
   (`Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion`,
   which computes both dimensions from generic points by [Stacks, Tag 0A21]).
3. `ℱ` extends to a coherent `𝒢` on `X̄` ([Stacks, Tag 0BK0],
   `AlgebraicGeometry.exists_isCoherent_restrict_iso`), and `H^d(X̄, 𝒢)` is finite-dimensional by
   [Stacks, Tag 02O6] over a field
   (`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`).
4. The restriction `H^d(X̄, 𝒢) → H^d(X, ℱ)` is surjective by clause (2) of [Stacks, Tag 0A3G]
   for the spectral space `X̄` of dimension at most `d`
   (`AlgebraicGeometry.finiteDimensional_cohomologyOverField_restrict_of_finiteType`).

This is exactly the source's last paragraph, with the projective closure `X̄'` of the Chow
modification replaced by the closure of `X` in a Nagata compactification; the induction on `d`,
the dévissage and the Leray step are not needed once the compactification exists.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `finiteDimensional_cohomologyOverField_of_isOpen_of_isProper`: for `Y` proper over `k` with
  `dim Y ≤ d`, an open `U ⊆ Y` and a coherent `ℱ` on `U`, `H^d(U, ℱ)` is finite-dimensional.
* `finiteDimensional_cohomologyOverField_of_isImmersion_of_isProper`: for a quasi-compact
  immersion `X ⟶ P` into a proper `k`-scheme with `dim X ≤ d`, `H^d(X, ℱ)` is finite-dimensional
  for every coherent `ℱ`.
* `finiteDimensional_topCohomology_of_isSeparated`: **[Stacks, Tag 0A3M]**.

## References

* [Stacks Project, Tag 0A3M](https://stacks.math.columbia.edu/tag/0A3M)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

/-- A scheme proper over a field is Noetherian. -/
private theorem isNoetherian_of_isProper {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsProper g] :
    IsNoetherian Y := by
  have : CompactSpace Y := (quasiCompact_iff_compactSpace g).mp inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  exact (isNoetherian_iff Y).2 ⟨inferInstance, inferInstance⟩

/-- **Top-degree finiteness on an open of a proper scheme over a field.** Let `g : Y ⟶ Spec k`
be proper with `dim(Y) ≤ d`, let `U ⊆ Y` be an open and let `ℱ` be a coherent `𝒪_U`-module.
Then `H^d(U, ℱ)` is a finite-dimensional `k`-vector space.

`ℱ` extends to a coherent module `𝒢` on `Y` by [Stacks, Tag 0BK0], `H^d(Y, 𝒢)` is
finite-dimensional by [Stacks, Tag 02O6], and clause (2) of [Stacks, Tag 0A3G], in the form
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_restrict_of_finiteType`, carries that
finiteness along the restriction to `U`. -/
theorem finiteDimensional_cohomologyOverField_of_isOpen_of_isProper {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsProper g] (U : Y.Opens) (F : U.toScheme.Modules) [F.IsCoherent]
    (d : ℕ) (hdim : topologicalKrullDim (Y : Type u) ≤ (d : WithBot ℕ∞)) :
    FiniteDimensional k (cohomologyOverField k (U.ι ≫ g) F d) := by
  have := isNoetherian_of_isProper k g
  have hU : IsCompact (U : Set Y) := NoetherianSpace.isCompact _
  obtain ⟨G, hGcoh, ⟨e⟩⟩ := exists_isCoherent_restrict_iso U hU F
  have : G.IsCoherent := hGcoh
  have hres : FiniteDimensional k
      (cohomologyOverField k (U.ι ≫ g) ((Scheme.Modules.restrictFunctor U.ι).obj G) d) :=
    finiteDimensional_cohomologyOverField_restrict_of_finiteType k g G d hdim U hU
      (finiteDimensional_cohomologyOverField_of_isProper k g G d)
  exact Module.Finite.equiv (cohomologyOverFieldIso k (U.ι ≫ g) e d).toLinearEquiv

/-- **Top-degree finiteness for a scheme quasi-compactly immersed in a proper scheme over a
field.** Let `p : P ⟶ Spec k` be proper, let `i : X ⟶ P` be a quasi-compact immersion, let `ℱ`
be a coherent `𝒪_X`-module and let `dim(X) ≤ d`. Then `H^d(X, ℱ)` is a finite-dimensional
`k`-vector space.

The scheme-theoretic image `X̄ = i.image` is a closed subscheme of `P`, hence proper over `k`,
and `X` is identified with the open `i.toImage.opensRange` of it: `i.toImage` is an open
immersion because `i` is a quasi-compact immersion, and it is dominant. So `dim X̄ ≤ dim X ≤ d`
by
`Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion`, and
`finiteDimensional_cohomologyOverField_of_isOpen_of_isProper` applies to `X̄`; the result is
transported back to `X` along `Scheme.Hom.isoOpensRange`. -/
theorem finiteDimensional_cohomologyOverField_of_isImmersion_of_isProper
    {P X : Scheme.{u}} (p : P ⟶ Spec (.of k)) [IsProper p] (i : X ⟶ P) [IsImmersion i]
    [QuasiCompact i] (F : X.Modules) [F.IsCoherent] (d : ℕ)
    (hdim : topologicalKrullDim (X : Type u) ≤ (d : WithBot ℕ∞)) :
    FiniteDimensional k (cohomologyOverField k (i ≫ p) F d) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  have : IsProper (i.imageι ≫ p) := inferInstance
  have := isNoetherian_of_isProper k (i.imageι ≫ p)
  have hfac : i.toImage ≫ (i.imageι ≫ p) = i ≫ p := Scheme.Hom.toImage_imageι_assoc _ _
  have hdimY : topologicalKrullDim (i.image : Type u) ≤ (d : WithBot ℕ∞) :=
    (Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion k
      i.toImage (i ≫ p) (i.imageι ≫ p) hfac i.toImage.denseRange).trans hdim
  have : ((Scheme.Modules.pushforward i.toImage.isoOpensRange.hom).obj F).IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite _ F
  have key : FiniteDimensional k (cohomologyOverField k
      (i.toImage.isoOpensRange.hom ≫ (i.toImage.opensRange.ι ≫ (i.imageι ≫ p))) F d) :=
    have := finiteDimensional_cohomologyOverField_of_isOpen_of_isProper k (i.imageι ≫ p)
      i.toImage.opensRange ((Scheme.Modules.pushforward i.toImage.isoOpensRange.hom).obj F) d
      hdimY
    Module.Finite.equiv (cohomologyOverFieldPushforwardIso k i.toImage.isoOpensRange.hom
      (i.toImage.opensRange.ι ≫ (i.imageι ≫ p)) F d).toLinearEquiv.symm
  have hcomm : i.toImage.isoOpensRange.hom ≫
      (i.toImage.opensRange.ι ≫ (i.imageι ≫ p)) = i ≫ p := by
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, hfac]
  rw [hcomm] at key
  exact key

/-- **[Stacks, Tag 0A3M].** Let `X` be a separated scheme of finite type over a field `k`, with
structure morphism `f : X ⟶ Spec k`, let `ℱ` be a coherent `𝒪_X`-module and let `d = dim(X)`.
Then `H^d(X, ℱ)` is a finite-dimensional `k`-vector space.

Nagata's compactification theorem ([Stacks, Tag 0F41],
`AlgebraicGeometry.hasCompactification_of_compactSpace_quasiSeparatedSpace`, applied over the
affine base `Spec k`) factors `f` as a quasi-compact open immersion followed by a proper
morphism, and `finiteDimensional_cohomologyOverField_of_isImmersion_of_isProper` applies. -/
@[stacks 0A3M "the full statement: for X separated and of finite type over a field k, F a \
  coherent O_X-module and d = dim X, the k-vector space H^d(X, F) is finite-dimensional"]
theorem finiteDimensional_topCohomology_of_isSeparated {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (F : X.Modules) [F.IsCoherent]
    (d : ℕ) (hd : topologicalKrullDim (X : Type u) = (d : WithBot ℕ∞)) :
    FiniteDimensional k (cohomologyOverField k f F d) := by
  obtain ⟨j, hj⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f
  have key := finiteDimensional_cohomologyOverField_of_isImmersion_of_isProper k j.toBase
    j.immersion F d hd.le
  rwa [show j.immersion ≫ j.toBase = f from Over.w j.obj.hom] at key

end AlgebraicGeometry

end
