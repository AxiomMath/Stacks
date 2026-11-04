module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitAffineOpensVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitGlobalSeparated
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitOpensSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitVanishingReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleInjectiveSystems
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit

/-!
# The colimit statement of Stacks 09YQ, unconditionally

`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_isLimit` is the colimit
statement of [Stacks, Tag 09YQ] on Mathlib's small étale sites in **every degree**, carrying no
hypothesis beyond the geometry the source itself assumes: a nonempty directed index, an inverse
system of quasi-compact quasi-separated schemes with affine transition morphisms, all of them and
the vertex of a limit cone objects of a big étale site.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_isLimit` — for every
  degree `p` and every presented system `E`, the cohomology `H^p(X, 𝒢)` of the limit is the
  filtered colimit of the `H^p(X_i, F_i)` along the legs.

## How the four hypotheses of the dévissage are supplied

`...isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic` is the dimension shift of the tag with
its dévissage and its vanishing hypothesis already discharged into geometry. Four hypotheses remain
there, and each is supplied by a theorem of the library:

* `H0`, the degree-zero statement, by `...isCohomologyColimit_zero_of_isLimit`;
* `haff`, acyclicity of the restriction of the colimit sheaf to each affine open of the limit, by
  `...QcqsLimitCohomology.subsingleton_H_smallEtaleOpensRestrict_of_pullbackPresentation`;
* `hsub`, the sections condition over the pairwise intersections, by
  `...AffineLimitCohomology.sectionsDifference_of_pullbackPresentation`;
* `H0EXZ`, [Stacks, Tag 0EXZ] levelwise, by `...hasPointwiseInjectiveEmbeddings`.

`haff` and `hsub` are stated at a system, a sheaf, a family of legs and the two clauses of the
presentation separately, while the dévissage quantifies over
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem`. The plumbing between the two
is the same three steps the degree-zero statement already uses: `...isColimitPresentation_iff`
splits the field `pres` into the compatibility clause and the pullback-colimit presentation,
`...isCompatibleFamily_iff` reads the first in the vocabulary of `...smallEtalePullbackAb`, and
`...transportLeg` is the family of legs in the form those two clauses are stated with.

## The two instances on the limit are derived, not assumed

The dévissage asks for `CompactSpace` and `QuasiSeparatedSpace` on the vertex. Both follow from the
per-level hypotheses and the limit property, so neither is carried here:

* quasi-compactness is `AlgebraicGeometry.Scheme.compactSpace_of_isLimit_of_initiallySmall`, which
  is Mathlib's `AlgebraicGeometry.Scheme.compactSpace_of_isLimit` with the three universes of the
  index type, the index morphisms and the schemes independent — the form this development needs,
  whose index is a `Type v` over schemes in `Scheme.{max u v}`. Its `CategoryTheory.InitiallySmall`
  price is paid by `CategoryTheory.initiallySmall_of_essentiallySmall`, the opposite of a directed
  preorder being thin and small;
* quasi-separatedness is Mathlib's `AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated` at any
  one projection of the cone, whose affineness — hence quasi-separatedness as a morphism — is
  `Stacks.EtaleCohomology.QcqsLimitCohomology.isAffineHom_limitProjection`. The index is nonempty,
  so there is a projection to take it at. This is the argument of
  `AlgebraicGeometry.Scheme.quasiSeparatedSpace_pt_of_isLimit`, which cannot be cited directly: it
  is stated for an index in the scheme universe, and here the index is a `Type v` while the schemes
  are `Scheme.{max u v}`.

`UnivLE.{v, max u v + 1}`, the universe side condition of the dévissage and of
[Stacks, Tag 0EXZ] levelwise, and the sheafification and `Ext` instances on the small étale sites
of the levels and of the limit, are all discharged by instance search at these variable indices;
none of them appears as a binder.

The `@[stacks 09YQ]` registration of the whole tag is the theorem below: it is stated at the
source's hypotheses, for all degrees `p` and every system of abelian sheaves in the sense of
[Stacks, Tag 0EZL], with the quasi-compactness and quasi-separatedness of the limit derived
rather than assumed.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EXZ](https://stacks.math.columbia.edu/tag/0EXZ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: 09YQ.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D) (B : BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]

include B hD hX hc in
/-- **[Stacks, Tag 09YQ] on Mathlib's small étale sites, in every degree, unconditionally.** Let
`I` be a nonempty directed index, let `(X_i)` be an inverse system of schemes over `Iᵒᵖ` with
**affine** transition morphisms and every `X_i` **quasi-compact and quasi-separated**, let `c` be a
**limit** cone with vertex `X`, and let all the `X_i` and `X` be objects of a big étale site `B`.
Then for every presented system `E` — a system `(F_i)` of abelian sheaves on Mathlib's small étale
sites of the `X_i` in the sense of [Stacks, Tag 0EZL], together with an abelian sheaf `𝒢` on the
small étale site of `X` and legs `ι_i : f_i^{-1}F_i ⟶ 𝒢` exhibiting `𝒢 = colim_i f_i^{-1}F_i` —
and every degree `p`, the cohomology `H^p(X, 𝒢)` is the filtered colimit of the `H^p(X_i, F_i)`
along the legs.

This is `isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic` with all four of its hypotheses
supplied; the module docstring says which theorem supplies each, and how the two instances
on the vertex are derived rather than assumed.

**No identity law** on the system of [Stacks, Tag 0EZL] is used or available: Definition 59.51.1 of
that tag imposes only the cocycle condition, and none of the four suppliers asks for more. -/
@[stacks 09YQ "the whole tag, for ALL degrees `p ≥ 0` and every system of abelian sheaves in the \
sense of Tag 0EZL, with no hypothesis beyond the source's. The source assumes a directed set, \
affine transition morphisms, `X = lim X_i` and that every `X_i` is quasi-compact and \
quasi-separated; those are `IsDirected`, `IsAffineHom (D.map a)`, `hc : IsLimit c`, and the \
per-level `CompactSpace`/`QuasiSeparatedSpace` instances. The big etale site `B` with `hD`/`hX` is \
a SIZE device and not a source hypothesis: it fixes which small sites are meant, and \
`AlgebraicGeometry.BigEtaleSite.exists_contains_of_small` produces one for any small family. The \
corresponding instances on the VERTEX are derived, not assumed. The conclusion is the tag's \
equality of groups in elementwise form -- joint surjectivity of the legs together with eventual \
vanishing, which for a filtered index and abelian coefficients is exactly the assertion that the \
cocone is colimiting -- and \
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimit_stableCohomologyCocone` transports it, \
in both directions, to a genuine `CategoryTheory.Limits.IsColimit` whose vertex is the full \
`H^p(X, 𝒢)`. No identity law is used: Definition 59.51.1 imposes only the cocycle condition, so \
the naive diagram `i ↦ H^p(X_i, F_i)` is not a functor in general, and \
`hasCohomologyIdentityLaw_iff_forall_stableCohomologySubgroup_eq_top` says precisely when the two \
spellings coincide. No hypothesis of this statement is an instance of its own conclusion."]
theorem isCohomologyColimit_of_isLimit (p : ℕ)
    (E : PresentedSystem (c := c) IsColimitPresentation) : IsCohomologyColimit E p := by
  have : InitiallySmall.{max u v} Iᵒᵖ := initiallySmall_of_essentiallySmall Iᵒᵖ
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit_of_initiallySmall D c hc
  have : IsAffineHom (c.π.app (op (Classical.arbitrary I))) :=
    QcqsLimitCohomology.isAffineHom_limitProjection D c hc _
  have : QuasiSeparatedSpace c.pt :=
    quasiSeparatedSpace_of_quasiSeparated (c.π.app (op (Classical.arbitrary I)))
  refine isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic
    (fun E' => isCohomologyColimit_zero_of_isLimit D c B hD hX hc E')
    (fun E' hinj V hV n hn => ?_) (fun E' hinj U V hU hV => ?_)
    (hasPointwiseInjectiveEmbeddings D) p E
  · obtain ⟨hcompat, hpres⟩ := (isColimitPresentation_iff E'.sys E'.sheaf E'.ι).mp E'.pres
    exact QcqsLimitCohomology.subsingleton_H_smallEtaleOpensRestrict_of_pullbackPresentation
      D c B hD hX hc E'.sys E'.sheaf hinj (transportLeg E'.sys E'.sheaf E'.ι) hpres
      ((isCompatibleFamily_iff E'.sys E'.sheaf E'.ι).mp hcompat) V hV n hn
  · obtain ⟨hcompat, hpres⟩ := (isColimitPresentation_iff E'.sys E'.sheaf E'.ι).mp E'.pres
    exact AffineLimitCohomology.sectionsDifference_of_pullbackPresentation
      D c B hD hX hc E'.sys E'.sheaf E'.ι hinj hpres
      ((isCompatibleFamily_iff E'.sys E'.sheaf E'.ι).mp hcompat) U V hU hV

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
