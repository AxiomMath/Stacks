module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.PurelyInseparableField
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalizationPurelyInseparable
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.RegularSmooth

/-!
# The normalization becomes smooth after a finite purely inseparable extension

Let `k` be a field and let `X` be a scheme of finite type over `k` of dimension at most one.
There is a finite purely inseparable extension `k'/k` such that the normalization of the base
change `X_{k'}` is *smooth* over `k'`. This is the first half of the construction of
[Stacks, Tag 0GK5]: its clause (1) (the extension), its clause (2) (the normalization) and the
smoothness of the normalization that the source establishes on the way to clause (5).

## Main results

* `isGeometricallyRegular_of_isGeometricallyNormal_of_topologicalKrullDim_le_one`: in dimension
  at most one geometric normality over a field implies geometric regularity.
* `smooth_of_isGeometricallyRegular`: a geometrically regular scheme locally of finite type over a
  field is smooth over that field.
* `exists_isPurelyInseparable_smooth_normalization`: the existence of the finite purely
  inseparable extension over which the normalization of the base change is smooth.

## Implementation notes

**Only part of [Stacks, Tag 0GK5] is established.** The source produces a whole diagram: a
finite purely inseparable `k'/k` (clause 1), the normalization `ν` of `X_{k'}` (clause 2), an
open immersion `j` with dense image of the disjoint union of the irreducible components of the
normalization into a disjoint union of compactifications (clause 3), finite separable extensions
`k'_i/k'` (clause 4), and the compactified pieces smooth, projective and geometrically
irreducible of dimension at most one over `k'_i` (clause 5). What is proved here is clause (1)
and clause (2) together with smoothness of `ν` over `k'`, the step the source takes with
Properties, Lemma 28.12.6 and Lemma 33.12.6. Clauses (3), (4) and (5) are *not* established:
they need the compactification of [Stacks, Tag 0BXW] over each `k'_i` and the global-sections
lemmas [Stacks, Tag 0BUG] and [Stacks, Tag 0FD1], and the attribute records this restriction.

**The separatedness hypothesis of the source is not needed for this part** and is therefore
omitted, which makes the statement more general; it is used in the source only to construct the
compactification of clause (3).

The route is the source's own. [Stacks, Tag 0BXT]
(`AlgebraicGeometry.exists_isPurelyInseparable_isGeometricallyNormal_normalization`) produces
`k'` with the normalization geometrically normal over `k'`. Normality and regularity agree in
dimension at most one ([Stacks, Tag 0BX2],
`AlgebraicGeometry.isRegularLocalRing_stalk_of_isNormal`), and the test extensions in the
criterion `AlgebraicGeometry.geometricallyRegularAt_tfae` for geometric regularity may be taken
finite purely inseparable, for which the base change is a homeomorphism
(`AlgebraicGeometry.isHomeomorph_pullbackFst_specMap_algebraMap`) and so preserves the dimension
bound. Geometric regularity is pointwise smoothness by [Stacks, Tag 038X]
(`AlgebraicGeometry.isGeometricallyRegularAt_iff_smoothAt`), and the smooth locus being
everything is smoothness. The dimension bound passes from `X` to `X_{k'}` because the base change
along a purely inseparable extension is a homeomorphism, and from `X_{k'}` to its normalization
because the normalization morphism is finite, hence integral ([Stacks, Tag 0ECG],
`AlgebraicGeometry.topologicalKrullDim_le_of_isIntegralHom`).

## References

* [Stacks Project, Tag 0GK5](https://stacks.math.columbia.edu/tag/0GK5)
* [Stacks Project, Tag 0BXT](https://stacks.math.columbia.edu/tag/0BXT)
* [Stacks Project, Tag 0BX2](https://stacks.math.columbia.edu/tag/0BX2)
* [Stacks Project, Tag 038X](https://stacks.math.columbia.edu/tag/038X)
* [Stacks Project, Tag 0ECG](https://stacks.math.columbia.edu/tag/0ECG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **In dimension at most one a geometrically normal scheme over a field is geometrically
regular.** By `AlgebraicGeometry.geometricallyRegularAt_tfae` it suffices to test regularity of
the local rings of the base change along finite purely inseparable extensions `K/k`. Such a base
change is a homeomorphism on underlying spaces, so it again has dimension at most one, and it is
normal because the original scheme is geometrically normal; normality and regularity agree in
dimension at most one. -/
public theorem isGeometricallyRegular_of_isGeometricallyNormal_of_topologicalKrullDim_le_one
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hgn : IsGeometricallyNormal f) :
    IsGeometricallyRegular f := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro x
  refine ((geometricallyRegularAt_tfae k X f x).out 2 1 rfl rfl).mp ?_
  intro K _ _ _ _ x' _
  have hnorm : ∀ z : (pullback f (spectrumMap k K) : Scheme.{u}),
      IsNormalRing ((pullback f (spectrumMap k K) : Scheme.{u}).presheaf.stalk z) := fun z =>
    hgn ((pullback.fst f (spectrumMap k K)).base z) K z rfl
  have _ : IsLocallyNoetherian (pullback f (spectrumMap k K) : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (spectrumMap k K))
  have _ : IsNormal (pullback f (spectrumMap k K) : Scheme.{u}) :=
    { stalk_isDomain := fun z => ((hnorm z).of_isLocalRing).1
      stalk_normal := fun z => ((hnorm z).of_isLocalRing).2 }
  exact isRegularLocalRing_stalk_of_isNormal (pullback f (spectrumMap k K) : Scheme.{u})
    ((IsHomeomorph.topologicalKrullDim_eq _
      (isHomeomorph_pullbackFst_specMap_algebraMap k K f)).le.trans hdim) x'

/-- **A geometrically regular scheme locally of finite type over a field is smooth over it.**
Geometric regularity at a point is smoothness at that point by [Stacks, Tag 038X], and a
morphism whose smooth locus is everything is smooth; the structure morphism is locally of finite
presentation because the base is Noetherian. -/
@[ega "IV 17.15.2" "partial",
  ega "IV 17.5.1" "b′⇒a, special case",
  sga "3 XI 1.2" "Proposition 1.2(i)"]
public theorem smooth_of_isGeometricallyRegular (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hf : IsGeometricallyRegular f) :
    Smooth f := by
  have _ : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  exact fun x _ => InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f x
    ((isGeometricallyRegularAt_iff_smoothAt f x).mp (hf x))

/-- **[Stacks, Tag 0GK5], clauses (1) and (2), with the normalization smooth over `k'`.** Let `k`
be a field and let `X` be a scheme of finite type over `k` with `dim X ≤ 1`. There is a finite
purely inseparable extension `k'/k` such that the normalization of `X_{k'}` is smooth over `k'`.

Clauses (3), (4) and (5) of the source — the compactification `j` with dense image, the finite
separable extensions `k'_i/k'` and the smooth projective geometrically irreducible pieces over
them — are not established here; see the module docstring. -/
@[stacks 0GK5
  "clauses (1) and (2), with ν smooth over k'; clauses (3), (4), (5) not established",
  sga "4 XIV 1.11"]
public theorem exists_isPurelyInseparable_smooth_normalization (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Module.Finite k k')
      (_ : IsPurelyInseparable k k'),
      Smooth (normalizationOverField k' (pullback.fst (spectrumMap k k') p) ≫
        pullback.fst (spectrumMap k k') p) := by
  obtain ⟨k', hfield, halg, hfin, hpi, hgn⟩ :=
    exists_isPurelyInseparable_isGeometricallyNormal_normalization k p
  refine ⟨k', hfield, halg, hfin, hpi, ?_⟩
  set q : pullback (spectrumMap k k') p ⟶ Spec (.of k') :=
    pullback.fst (spectrumMap k k') p
  -- The base change to `k'` is homeomorphic to `X`, hence again of dimension at most one.
  have hdimXk : topologicalKrullDim ((pullback (spectrumMap k k') p : Scheme.{u}) : Type u) ≤ 1 :=
    ((IsHomeomorph.topologicalKrullDim_eq _
      (pullbackSymmetry (spectrumMap k k') p).hom.homeomorph.isHomeomorph).trans
      (IsHomeomorph.topologicalKrullDim_eq _
        (isHomeomorph_pullbackFst_specMap_algebraMap k k' p))).le.trans hdim
  -- The normalization morphism is finite, hence does not raise the dimension.
  have _ : IsFinite (normalizationOverField k' q) := isFinite_normalizationOverField k' q
  have hdimY : topologicalKrullDim (normalizationSchemeOverField k' q) ≤ 1 :=
    (topologicalKrullDim_le_of_isIntegralHom (normalizationOverField k' q)).trans hdimXk
  exact smooth_of_isGeometricallyRegular k' (normalizationOverField k' q ≫ q)
    (isGeometricallyRegular_of_isGeometricallyNormal_of_topologicalKrullDim_le_one k'
      (normalizationOverField k' q ≫ q) hdimY hgn)

end AlgebraicGeometry

end
