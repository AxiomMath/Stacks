module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TriangleAdditivity
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedRoof
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# Additivity across a triangle from an envelope onto a scheme with the resolution property

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished triangle in `D(𝒪_X)`
with `E₁` and `E₂` perfect. The last paragraph of the proof of [Stacks, Tag 0F9F] reduces its
conditions (3) and (4) to its condition (1) by producing an envelope `f : Y ⟶ X` whose target
is a disjoint union of quasi-compact quasi-separated schemes with the resolution property, and
then representing `Lf^*E₁ ⟶ Lf^*E₂` by a map of bounded complexes of finite locally free
modules by [Stacks, Tag 0F8I].

This file carries out the second half of that reduction: on such a `Y` the map
`Lf^*E₁ ⟶ Lf^*E₂` really is represented by a map of bounded complexes of finite locally free
`𝒪_Y`-modules, so condition (1) holds and the conclusion of Stacks 0F9F follows.

## Main results

* `Stacks.Chow.triangleChernAdditive_of_resolutionProperty_envelope` — the conclusion of
  Stacks 0F9F for a triangle admitting an envelope onto a quasi-compact, quasi-separated,
  semi-separated scheme with the resolution property.
* `Stacks.Chow.isLocallyBoundedFiniteLocallyFree_of_boundedFiniteLocallyFreeComplex` — a
  bounded complex of finite locally free modules, in the sense the categories of Stacks 0F8I
  are built from, is locally bounded of finite locally free terms in the sense the Chern
  classes of Stacks 0F9E are read at.

## Implementation notes

The two inputs from Stacks 0F8I, both in the namespace
`Stacks.Perfect.BoundedLocallyFreeComplexes`, are its essential surjectivity
(`exists_boundedFiniteLocallyFree_iso_of_affineDiagonal`, Stacks 0F8F) and its fullness
(`exists_boundedFiniteLocallyFree_roof_of_affineDiagonal`, Stacks 0F8G). Each is used in the form
stated for a scheme with affine diagonal, which needs no hypothesis beyond the ones displayed
here; the forms stated for a scheme with the resolution property alone derive the affine diagonal
from Stacks 0F8C and carry that tag's hypothesis. Affine diagonal is the
`IsAffineHom (pullback.diagonal (terminal.from Y))` hypothesis below, semi-separatedness of `Y`.

Fullness is used through the roof it produces: a morphism `Lf^*E₁ ⟶ Lf^*E₂` read between
bounded representatives `ℰ^•` of the first and `ℱ^•` of the second is
`inv(Q(p)) ≫ Q(q)` for a bounded complex `𝒢^•` of finite locally free modules, a
quasi-isomorphism `p : 𝒢^• ⟶ ℰ^•` and a map `q : 𝒢^• ⟶ ℱ^•`. Then `q` is a map of complexes
representing `Lf^*E₁ ⟶ Lf^*E₂`, with `𝒢^•` in place of `ℰ^•` as the representative of
`Lf^*E₁`, and `Stacks.Chow.hasDefinedChernClasses_and_additive_of_envelope` applies.

Perfectness of `Lf^*E₁` and `Lf^*E₂`, which is what the two inputs ask for, comes from
perfectness of `E₁` and `E₂` by
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback` (Stacks 09UA).
Perfectness of `E₃` is not needed: the third object enters only through the cone of `q`.

What this does not do is produce the envelope. For conditions (3) and (4) of Stacks 0F9F the
source builds it from Stacks 0GTU, which gives an envelope onto a scheme with an ample family of
invertible modules, and Stacks 0GMM, which gives that scheme the resolution property.

For condition (4) that envelope is now built, in
`StacksFrontier/AlgebraicGeometry/Chow/ChernClassDerived/TriangleAdditivityQuasiCompact.lean`. Two
of the three things that stood in the way are no longer missing. Semi-separatedness of the
envelope's source is not needed separately: the source is Noetherian, being the source of a
proper morphism onto a Noetherian scheme, and a Noetherian scheme with the resolution property
has affine diagonal by the Noetherian case of Stacks 0F8C
(`AlgebraicGeometry.isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian`, which carries
no hypothesis). The substantial direction of Stacks 0F89 is not needed in the generality in which
`AlgebraicGeometry.hasResolutionProperty_of_isAmpleFamily` asks for it, namely for every scheme:
its Noetherian case is proved, as
`AlgebraicGeometry.hasResolutionProperty_of_epi_idealPow_of_isNoetherian`, and that is the case
the envelope's source falls under. The third, the other input of Stacks 0GMM — the sheaf of
ideals cut out by a global section of an invertible module — is
`AlgebraicGeometry.existsSectionImageIdeal`, proved in
`StacksFrontier/AlgebraicGeometry/Perfect/SectionImageIdeal.lean`. So condition (4) of Stacks 0F9F
is registered, at `Stacks.Chow.triangleChernAdditive_of_compactSpace`, on the source's own
hypotheses.

**Condition (3) is now registered**, at
`Stacks.Chow.triangleChernAdditive_of_isCompact_irreducibleComponents` in
`StacksFrontier/AlgebraicGeometry/Chow/ChernClassDerived/TriangleAdditivityComponents.lean`. The
geometry was already built: a locally Noetherian scheme whose irreducible components are
quasi-compact is the target of an envelope whose source is a coproduct of Noetherian schemes
with the resolution property and affine diagonal
(`Stacks.Chow.exists_isEnvelope_sigma_of_isCompact_irreducibleComponents`, in
`StacksFrontier/AlgebraicGeometry/Chow/ChernClassDerived/ComponentEnvelope.lean`). So was the
*object*-level derived algebra over such a source, which is
`Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_iso_derivedPullback_sigma` in
`StacksFrontier/AlgebraicGeometry/Chow/ChernClassDerived/CriteriaComponents.lean`: degreewise
restriction to the summands is an equivalence on complexes
(`AlgebraicGeometry.sigmaComplexEquivalence`), so the summands' bounded complexes of finite
locally free modules assemble into one complex on `∐ X'ᵢ`, and the isomorphism in
`D(𝒪_{∐ X'ᵢ})` is built from the summands' isomorphisms read as roofs of actual complexes. That
is clause (3) of Stacks 0GUE.

What condition (3) of Stacks 0F9F asks for beyond this is the *commuting square*: the map
`α : 𝓔₁^• ⟶ 𝓔₂^•` glued from the summands' maps has to represent `Lf^*E₁ ⟶ Lf^*E₂`, which is an
equation in `D(𝒪_{∐ X'ᵢ})`, and each summand's own square gives that equation only after
restriction. There is no identification of `D(𝒪_{∐ X'ᵢ})` with the product of the `D(𝒪_{X'ᵢ})`;
what supplies the equation instead is that the derived pullbacks to the summands are jointly
**faithful** (`AlgebraicGeometry.eq_of_forall_derivedPullback_sigmaι_map_eq`, in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/SigmaDerivedCategory.lean`), so an equation
between two morphisms of `D(𝒪_{∐ X'ᵢ})` may be checked summand by summand.

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 0F8G](https://stacks.math.columbia.edu/tag/0F8G)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-- A bounded complex of finite locally free modules, in the sense of the categories of
[Stacks, Tag 0F8I], is a locally bounded complex of finite locally free modules in the sense
the Chern classes of [Stacks, Tag 0F9E] are read at: the two boundedness conditions give the
global bounds, which work on the open `⊤` around every point, and the two finite-local-freeness
classes of this development have the same single field. -/
theorem isLocallyBoundedFiniteLocallyFree_of_boundedFiniteLocallyFreeComplex {Y : Scheme.{u}}
    {P : CochainComplex Y.Modules ℤ} (hP : boundedFiniteLocallyFreeComplex Y P) :
    IsLocallyBoundedFiniteLocallyFree P := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hflf⟩ := hP
  exact isLocallyBoundedFiniteLocallyFree_of_bounded P ⟨a, b, ha, hb⟩
    fun n => ⟨(hflf n).exists_isFiniteLocallyFreeData⟩

/-- **The conclusion of [Stacks, Tag 0F9F] from an envelope onto a scheme with the resolution
property.** Let `T` be a distinguished triangle of `D(𝒪_X)` whose first two objects are
perfect. If there is an envelope `f : Y ⟶ X` with `Y` quasi-compact, quasi-separated,
semi-separated and carrying the resolution property, then the Chern classes of `E₁`, `E₂`, `E₃`
are defined and

  `c(E₂) = c(E₁) c(E₃)`,  `ch_p(E₂) = ch_p(E₁) + ch_p(E₃)`,  `P_p(E₂) = P_p(E₁) + P_p(E₃)`.

The derived pullbacks `Lf^*E₁` and `Lf^*E₂` are perfect, so each is isomorphic to a bounded
complex of finite locally free `𝒪_Y`-modules by [Stacks, Tag 0F8F], and the morphism between
them is represented by a roof with a quasi-isomorphism on the left by [Stacks, Tag 0F8G]; the
right leg of that roof is a map of bounded — hence locally bounded — complexes of finite
locally free modules representing `Lf^*E₁ ⟶ Lf^*E₂`, which is condition (1) of the source. -/
theorem triangleChernAdditive_of_resolutionProperty_envelope
    (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (T : Triangle (DerivedCategory X.Modules))
    (hT : T ∈ distTriang (DerivedCategory X.Modules))
    {Y : Scheme.{u}} (f : Y ⟶ X) (hf : IsEnvelope f)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [HasResolutionProperty Y]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (h₁ : IsPerfect (X := X.toRingedSpace) T.obj₁)
    (h₂ : IsPerfect (X := X.toRingedSpace) T.obj₂) :
    TriangleChernAdditive C sX T := by
  obtain ⟨E, hE, ⟨iE⟩⟩ := exists_boundedFiniteLocallyFree_iso_of_affineDiagonal Y _
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      f.toLRSHom.toShHom T.obj₁ h₁)
  obtain ⟨F, hF, ⟨iF⟩⟩ := exists_boundedFiniteLocallyFree_iso_of_affineDiagonal Y _
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      f.toLRSHom.toShHom T.obj₂ h₂)
  obtain ⟨G, p, hp, q, hG, hroof⟩ := exists_boundedFiniteLocallyFree_roof_of_affineDiagonal Y E F
    hE hF (iE.hom ≫ (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).map T.mor₁ ≫ iF.inv)
  have hpIso : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso Y.Modules p).2 hp
  have hq : DerivedCategory.Q.map q = DerivedCategory.Q.map p ≫ iE.hom ≫
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).map T.mor₁ ≫ iF.inv := by
    rw [← hroof, IsIso.hom_inv_id_assoc]
  refine hasDefinedChernClasses_and_additive_of_envelope C sX T hT f hf q
    (isLocallyBoundedFiniteLocallyFree_of_boundedFiniteLocallyFreeComplex hG)
    (isLocallyBoundedFiniteLocallyFree_of_boundedFiniteLocallyFreeComplex hF)
    (asIso (DerivedCategory.Q.map p) ≪≫ iE).symm iF.symm ?_
  exact (asIso (DerivedCategory.Q.map p) ≪≫ iE).inv_comp_eq.2
    (hq.trans (Category.assoc _ _ _).symm)

end Stacks.Chow
