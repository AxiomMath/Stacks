module

public import StacksFrontier.AlgebraicGeometry.Properties.DimensionZero
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsDimensionInduction
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Dimension zero: a proper geometrically integral scheme of dimension zero over a field is its base

Let `k` be a field and let `X` be a scheme proper and geometrically integral over `k` whose
underlying space has topological Krull dimension zero. Then the structure morphism
`f : X ⟶ Spec k` is an isomorphism. Two known results compose to give this and nothing further is
needed: dimension zero plus quasi-compactness and quasi-separatedness, both of which properness
supplies, make `X` affine (Stacks Tag 0CKV), and properness plus geometric integrality make the
canonical homomorphism `k ⟶ Γ(X, 𝒪_X)` an isomorphism (clause (8) of Stacks Tag 0BUG). A morphism
of affine schemes inducing an isomorphism on global sections is an isomorphism.

The consequence this file is written for is the **dimension-zero instance of the statement the
induction of Stacks Tag 0FH7 runs on**. If `f` is an isomorphism it is a monomorphism, so the two
`k`-rational points of `X` are the same morphism, their classes in `CH_0(X)` are the same class,
and the difference is `0 = n · 0`. That is
`Stacks.WeilCohomology.RationalPointDifferenceDivisible k n 0`, which until now was missing and
was the whole reason
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_of_dimOne` had to be based at dimension
one and the assembled statement of the tag had to carry a hypothesis excluding dimension zero.

## Main results

* `AlgebraicGeometry.isIso_of_topologicalKrullDim_eq_zero` — a proper geometrically integral
  scheme of dimension zero over a field has an isomorphism for its structure morphism.
* `Stacks.WeilCohomology.rationalPointDifferenceDivisible_zero` — the dimension-zero instance of
  the statement of Stacks Tag 0FH7, proved outright.

## Implementation notes

The first result is stated at the hypotheses its proof uses — `IsProper` and
`GeometricallyIntegral` — rather than at the smooth geometrically irreducible shape its consumer
has; the consumer supplies geometric reducedness from smoothness by
`AlgebraicGeometry.geometricallyReduced_of_smooth` and then geometric integrality by
`AlgebraicGeometry.GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible`. At
dimension zero this costs no generality: a reduced connected point is integral.

There is a second route to the first result which this file does not take.
`AlgebraicGeometry.isIso_of_etale_of_isSeparated_of_geometricallyIrreducible` needs no dimension
hypothesis at all, so an étale separated geometrically irreducible morphism is already an
isomorphism; dimension zero would enter only through smooth plus dimension zero implying étale.
That implication is proved three times in this library and is `private` every time, so the route is
not available, whereas the two results composed below are public.

No Stacks tag is registered here. The content is the composition of Stacks Tag 0CKV, registered on
`AlgebraicGeometry.isAffine_of_topologicalKrullDim_eq_zero`, with clause (8) of Stacks Tag 0BUG,
registered on `AlgebraicGeometry.isIso_globalSections_of_geometricallyIntegral`; neither tag's
statement is what is proved here, and the dimension-zero case of Stacks Tag 0FH7 is not a tag of
its own.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0CKV](https://stacks.math.columbia.edu/tag/0CKV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A proper geometrically integral scheme of dimension zero over a field is its own base.** Let
`k` be a field and let `f : X ⟶ Spec k` be proper and geometrically integral with
`topologicalKrullDim X = 0`. Then `f` is an isomorphism.

Properness gives `X` a compact and quasi-separated space, so dimension zero makes `X` affine by
Stacks Tag 0CKV; properness and geometric integrality make `k ⟶ Γ(X, 𝒪_X)` an isomorphism by
clause (8) of Stacks Tag 0BUG. Both `X` and `Spec k` being affine, the naturality square
`AlgebraicGeometry.Scheme.isoSpec_hom_naturality` writes `f` as an isomorphism composed with
`Spec` of that isomorphism composed with an isomorphism. -/
theorem isIso_of_topologicalKrullDim_eq_zero (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [GeometricallyIntegral f]
    (hdim : topologicalKrullDim X = 0) : IsIso f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : IsAffine X := isAffine_of_topologicalKrullDim_eq_zero X hdim
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_geometricallyIntegral k f
  have : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv f.appTop
  have hnat := Scheme.isoSpec_hom_naturality (X := X) (Y := Spec (.of k)) f
  have : IsIso (f ≫ (Spec (.of k)).isoSpec.hom) := by rw [← hnat]; infer_instance
  exact IsIso.of_isIso_comp_right f (Spec (.of k)).isoSpec.hom

end AlgebraicGeometry

namespace Stacks.WeilCohomology

/-- **The dimension-zero instance of the statement [Stacks, Tag 0FH7] inducts on, proved.** On a
proper smooth geometrically irreducible `k`-scheme `X` with `topologicalKrullDim X = 0` the
difference of the classes of two `k`-rational points is divisible by every integer `n`, because it
is zero.

Smoothness gives geometric reducedness, which with geometric irreducibility gives geometric
integrality, so `AlgebraicGeometry.isIso_of_topologicalKrullDim_eq_zero` makes the structure
morphism an isomorphism and in particular a monomorphism. The two rational points are sections of
it, hence equal, hence have the same class, and the difference of a class with itself is `0 = n·0`.

Neither separable closedness of `k` nor invertibility of `n` is used: both are hypotheses of
[Stacks, Tag 0FH7] needed for the dimension-one instance, and dimension zero needs neither. -/
theorem rationalPointDifferenceDivisible_zero (k : Type u) [Field k] (n : ℤ) :
    RationalPointDifferenceDivisible k n 0 := by
  unfold RationalPointDifferenceDivisible
  intro X f _ _ _ hdim x x' hx hx'
  have : GeometricallyReduced f := geometricallyReduced_of_smooth f
  have : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have : IsIso f := isIso_of_topologicalKrullDim_eq_zero k f (by simpa using hdim)
  obtain rfl : x = x' := (cancel_mono f).mp (hx.trans hx'.symm)
  exact ⟨0, by rw [smul_zero]; exact sub_self _⟩

end Stacks.WeilCohomology

end
